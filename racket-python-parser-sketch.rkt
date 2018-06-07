#lang racket


#; (process-py path-to-python-source
               racket-parser-fn
               path-to-output-file)

#; (define (process-py path-source parser path-target)
     ; make syscall to python-parse-to-json
     ; get json output of that call
     ; parse json to jsexpr (requrie json
     ; trim uneeded data
     ; parse jsexpr to py-sexpr
     ; apply parser fn
     ; parse to string
     ; save to output path
     )