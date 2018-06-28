#lang racket
(require json)

#| SNEKET

This file represents a feasibility study for developing
a racket-based tool to parse and emit python source code.

As of now, I use Philip Guo's parser-wrapper to convert
a python source file to JSON format:

- https://github.com/pgbovine/python-parse-to-json

The below consists of functions to process that output,
first using racket/json to convert the JSON to a nested
racket hash table. These functions include filters to omit
unwanted fields, a converter to s-expression format:

  (Node-name (field-name values ...) ...)

Or, optionally, with field-names omitted. Note that fields
can contains lists. The preceeding functions are generic
in that they do not depend on specific Node and Field
types. There is also a rendering funtion, which produces
pythong code from the above s-expression format, but this
is NOT generic, and only implements the Node and field types
present in the concrete example below.

Note: The provided example, including the JSON AST at the
bottom of this file\, is from Philip Guo as linked above.

|#



#| The tests below shows a representation
   of the following python source:

def foo(a, b, *c):
   y = a + (b - c)
   return y

|#



(module+ test
  (require rackunit)

  (define python-sample
    "def foo(a, b, *c):\n   y = a + (b - c)\n   return y\n")

  #| full sexpr-AST with field names |#
  (check-equal? (string->explicit-sexpr sample-json)
                '(Module
                  (body
                   (FunctionDef
                    (body
                     (Assign
                      (targets (Name (id "y")))
                      (value
                       (BinOp
                        (right
                         (BinOp (right (Name (id "c")))
                                (left (Name (id "b")))
                                (op (Sub))))
                        (left (Name (id "a")))
                        (op (Add)))))
                     (Return (value (Name (id "y")))))
                    (name "foo")
                    (args
                     (arguments
                      (args (arg (arg "a"))
                            (arg (arg "b")))
                      (vararg (arg (arg "c")))))))))

  #| reduced sexpr-AST.
     here, field names are ommitted.
     note that some nodes have bad default ordering. |#
  
  (check-equal? (string->implicit-sexpr sample-json)
                '(Module
                  (FunctionDef
                   "foo"
                   (arguments ((arg "a")
                               (arg "b"))
                              (arg "c"))
                   ((Assign
                     (Name "y")
                     (BinOp (Add)
                            (Name "a")
                            (BinOp (Sub)
                                   (Name "b")
                                   (Name "c"))))
                    (Return (Name "y"))))))

  
  #| reduced version but with system call
     to generate json. only tested in linux |#

  (check-equal? (string->implicit-sexpr (python->json python-sample))
                '(Module
                  (FunctionDef
                   "foo"
                   (arguments ((arg "a")
                               (arg "b"))
                              (arg "c"))
                   ((Assign
                     (Name "y")
                     (BinOp (Add)
                            (Name "a")
                            (BinOp (Sub)
                                   (Name "b")
                                   (Name "c"))))
                    (Return (Name "y"))))))

  
  #| pretty-print test using explicit form  |#  
  
  (check-equal? (render (string->explicit-sexpr sample-json))
                "def foo(a, b, *c):\n   y = (a + (b - c))\n   return y\n"))



#| python->json : sting → string
     Calls external python parser|#
(define (python->json str)
  (define parser-path
    "python python-parse-to-json/parse_python_to_json.py")
  (first (string-split
          (with-output-to-string
            (λ ()
              (system
               (string-append parser-path " '" str "'"))))
          "\n")))


#| filter-fields : [symbols] → (jsexpr → jsexpr)
     recursively removes specified fields
     from the hash|#

(define ((filter-fields fields) hs)
  (for/fold ([acc #hasheq()])
            ([(k v) hs])
    (match* (k v)
      [((? (curryr member fields)) _)
       acc]
      [(_ (? hash?))
       (hash-set acc k ((filter-fields fields) v))]
      [(_ (? list?))
       (hash-set acc k (map (filter-fields fields) v))]
      [(_ _)
       (hash-set acc k v)])))


#| filter-fields-safe : jsexpr → jsexpr
     this removes source location information
     and the list of fields. the former is
     potentially useful for dispatch, but
     can probably be reconstructed from the
     fields themselves |#

(define filter-fields-safe
  (filter-fields '(loc
                   _fields)))


#| filter-fields-risky : jsexpr → jsexpr
     this removes a variety of fields which
     may or may not be important based on
     use-case. intended mostly for demonstation;
     these choices are not partiualy thought-out.|#

(define (filter-fields-risky hs)
  (unless (hash-has-key? hs 'type)
    (error "no type field"))
  ((filter-fields '(; these are fn def fields:
                    kw_defaults
                    kwarg
                    defaults
                    kwonlyargs
                    decorator_list
                    ; ctx has various uses:
                    ctx
                    ; type annotations:
                    annotation
                    ; return type annotation:
                    returns))
   hs))


#| hash->sexpr : jsexpr → sexpr
     recursively converts a jsexpr into an
     sexpr of the form (Node (key value) ...) |#

(define (hash->sexpr hs)
  (match hs
    [(hash-table ('type t) other-fields ...)
     (define the-rest
       (for/list ([field other-fields])
         (match field
           [`(,k ,(? hash? v))
            `(,k ,(hash->sexpr v))]
           [`(,k ,(? list? v))
            `(,k ,@(map hash->sexpr v))]
           [`(,k ,v)
            `(,k ,v)])))
     `(,(string->symbol t) ,@the-rest)]))


#| reorder-some-nodes : sexpr → sexpr
     This is an ad-hoc reordering of fields
     for some node types to permit unambiguous
     elision of field-names |#

(define (reorder-some-nodes stx)
  (match stx
    [`(BinOp (right ,a)
             (left ,b)
             (op ,c))
     (reorder-some-nodes `(BinOp (op ,c)
                                 (left ,b)
                                 (right ,a)))]
    [`(FunctionDef
       (body ,a ...)
       (name ,b)
       (args ,c))
     (reorder-some-nodes `(FunctionDef
                           (name ,b)
                           (args ,c)
                           (body ,@a)))]
    [(? list?) (map reorder-some-nodes stx)]
    [_ stx]))


#| implicitize-fields : sexpr → sexpr
     Simplifies the presentation by omitting
     field names. we'd want to establish a
     canonical order on fields before doing this. |#

(define (implicitize-fields stx)
  (match stx
    [`(,form-name (,field-names
                   ,(app implicitize-fields fields) ...)
                  ...)
     #| this is kind of a discount way on handling multi-node fields |#
     `(,form-name ,@(for/list ([f fields])
                      (if (equal? 1 (length f)) (first f) f)))]
    [(? string?) stx]))


#| putting it all together |#

(define string->implicit-sexpr
  (compose implicitize-fields
           reorder-some-nodes
           hash->sexpr
           filter-fields-risky
           filter-fields-safe
           string->jsexpr))

(define string->explicit-sexpr
  (compose hash->sexpr
           filter-fields-risky
           filter-fields-safe
           string->jsexpr))


#| render : sexpr → string
     Renders the full (with fields) sexprn format
     to a string which hopefully represents
     valid python code |#

(define (render stx)
  (define R render)
  (match stx
    [`(Add) "+"]
    [`(Sub) "-"]
    [`(Name (id ,id)) id]
    [`(arg (arg ,arg)) arg]
    [`(Return (value ,(app R value)))
     (string-append "return " value)]
    [`(Module (body ,(app R body) ...))
     (apply string-append body)]
    [`(Assign
       (targets ,(app R targets))
       (value ,(app R value)))
     (string-append targets " = " value)]
    [`(BinOp
       (right ,(app R right))
       (left ,(app R left))
       (op ,(app R op)))
     (string-append "(" left " " op " " right ")")]
    [`(FunctionDef (body ,(app R body) ...)
                   (name ,name)
                   (args ,(app R args)))
     (apply string-append "def " name
            "(" args "):\n"
            (map (λ (x) (string-append "   " x "\n" )) body))]
    ; the next two don't have capitalized types for some reason?
    [`(arguments (args ,(app R args) ...)
                 (vararg ,(app R varargs) ...))
     (string-trim
      (apply string-append
             (append (map (λ (x) (string-append x ", " )) args)
                     (map (λ (x) (string-append "*" x ", " )) varargs)))
      ", ")]))




(define sample-json
  "{
  \"body\": [
    {
      \"body\": [
        {
          \"loc\": {
            \"start\": {
              \"column\": 2,
              \"line\": 3
            },
            \"end\": {
              \"column\": 16,
              \"line\": 3
            }
          },
          \"_fields\": [
            \"targets\",
            \"value\"
          ],
          \"type\": \"Assign\",
          \"targets\": [
            {
              \"ctx\": null,
              \"loc\": {
                \"start\": {
                  \"column\": 2,
                  \"line\": 3
                },
                \"end\": {
                  \"column\": 3,
                  \"line\": 3
                }
              },
              \"_fields\": [
                \"id\",
                \"ctx\"
              ],
              \"type\": \"Name\",
              \"id\": \"y\"
            }
          ],
          \"value\": {
            \"loc\": {
              \"start\": {
                \"column\": 6,
                \"line\": 3
              },
              \"end\": {
                \"column\": 16,
                \"line\": 3
              }
            },
            \"right\": {
              \"loc\": {
                \"start\": {
                  \"column\": 11,
                  \"line\": 3
                },
                \"end\": {
                  \"column\": 16,
                  \"line\": 3
                }
              },
              \"right\": {
                \"ctx\": null,
                \"loc\": {
                  \"start\": {
                    \"column\": 15,
                    \"line\": 3
                  },
                  \"end\": {
                    \"column\": 16,
                    \"line\": 3
                  }
                },
                \"_fields\": [
                  \"id\",
                  \"ctx\"
                ],
                \"type\": \"Name\",
                \"id\": \"c\"
              },
              \"left\": {
                \"ctx\": null,
                \"loc\": {
                  \"start\": {
                    \"column\": 11,
                    \"line\": 3
                  },
                  \"end\": {
                    \"column\": 12,
                    \"line\": 3
                  }
                },
                \"_fields\": [
                  \"id\",
                  \"ctx\"
                ],
                \"type\": \"Name\",
                \"id\": \"b\"
              },
              \"_fields\": [
                \"left\",
                \"op\",
                \"right\"
              ],
              \"type\": \"BinOp\",
              \"op\": {
                \"loc\": {
                  \"start\": {
                    \"column\": 13,
                    \"line\": 3
                  },
                  \"end\": {
                    \"column\": 14,
                    \"line\": 3
                  }
                },
                \"_fields\": [],
                \"type\": \"Sub\"
              }
            },
            \"left\": {
              \"ctx\": null,
              \"loc\": {
                \"start\": {
                  \"column\": 6,
                  \"line\": 3
                },
                \"end\": {
                  \"column\": 7,
                  \"line\": 3
                }
              },
              \"_fields\": [
                \"id\",
                \"ctx\"
              ],
              \"type\": \"Name\",
              \"id\": \"a\"
            },
            \"_fields\": [
              \"left\",
              \"op\",
              \"right\"
            ],
            \"type\": \"BinOp\",
            \"op\": {
              \"loc\": {
                \"start\": {
                  \"column\": 8,
                  \"line\": 3
                },
                \"end\": {
                  \"column\": 9,
                  \"line\": 3
                }
              },
              \"_fields\": [],
              \"type\": \"Add\"
            }
          }
        },
        {
          \"loc\": {
            \"start\": {
              \"column\": 2,
              \"line\": 4
            },
            \"end\": {
              \"column\": 10,
              \"line\": 4
            }
          },
          \"_fields\": [
            \"value\"
          ],
          \"type\": \"Return\",
          \"value\": {
            \"ctx\": null,
            \"loc\": {
              \"start\": {
                \"column\": 9,
                \"line\": 4
              },
              \"end\": {
                \"column\": 10,
                \"line\": 4
              }
            },
            \"_fields\": [
              \"id\",
              \"ctx\"
            ],
            \"type\": \"Name\",
            \"id\": \"y\"
          }
        }
      ],
      \"loc\": {
        \"start\": {
          \"column\": 0,
          \"line\": 2
        },
        \"end\": {
          \"column\": 10,
          \"line\": 4
        }
      },
      \"name\": \"foo\",
      \"args\": {
        \"loc\": {
          \"start\": {
            \"column\": 8,
            \"line\": 2
          },
          \"end\": {
            \"column\": 16,
            \"line\": 2
          }
        },
        \"vararg\": {
          \"loc\": {
            \"start\": {
              \"column\": 15,
              \"line\": 2
            },
            \"end\": {
              \"column\": 16,
              \"line\": 2
            }
          },
          \"_fields\": [
            \"arg\",
            \"annotation\"
          ],
          \"type\": \"arg\",
          \"annotation\": null,
          \"arg\": \"c\"
        },
        \"args\": [
          {
            \"loc\": {
              \"start\": {
                \"column\": 8,
                \"line\": 2
              },
              \"end\": {
                \"column\": 9,
                \"line\": 2
              }
            },
            \"_fields\": [
              \"arg\",
              \"annotation\"
            ],
            \"type\": \"arg\",
            \"annotation\": null,
            \"arg\": \"a\"
          },
          {
            \"loc\": {
              \"start\": {
                \"column\": 11,
                \"line\": 2
              },
              \"end\": {
                \"column\": 12,
                \"line\": 2
              }
            },
            \"_fields\": [
              \"arg\",
              \"annotation\"
            ],
            \"type\": \"arg\",
            \"annotation\": null,
            \"arg\": \"b\"
          }
        ],
        \"kwarg\": null,
        \"defaults\": [],
        \"kw_defaults\": [],
        \"kwonlyargs\": [],
        \"_fields\": [
          \"args\",
          \"vararg\",
          \"kwonlyargs\",
          \"kwarg\",
          \"defaults\",
          \"kw_defaults\"
        ],
        \"type\": \"arguments\"
      },
      \"returns\": null,
      \"_fields\": [
        \"name\",
        \"args\",
        \"returns\",
        \"body\",
        \"decorator_list\"
      ],
      \"type\": \"FunctionDef\",
      \"decorator_list\": []
    }
  ],
  \"loc\": {
    \"start\": {
      \"column\": 0,
      \"line\": 2
    },
    \"end\": {
      \"column\": 10,
      \"line\": 4
    }
  },
  \"_fields\": [
    \"body\"
  ],
  \"type\": \"Module\"
}")




