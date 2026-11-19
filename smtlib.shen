\\ Raw SMT-LIB reader and sort checking. Every encoded term is [bool L]
\\ or [bv | Bits], with bit-vector literals stored least significant first.

(define smt.bv
  Bits -> (do (smt.width (length Bits)) [bv | Bits]))

(define smt.literal
  ["#" "b" | Digits] -> (smt.bv (map (/. D (smt.bit-char D)) (reverse Digits)))
  ["#" "x" | Digits] -> (smt.bv (smt.hex-bits (reverse Digits)))
  _ -> false)

(define smt.var-name?
  X -> (and (symbol? X) (not (= X (intern "_")))))

(define smt.lookup
  Name [[Name Value] | _] -> Value
  Name [_ | Rest] -> (smt.lookup Name Rest)
  _ [] -> false)

(define smt.make-binding
  _ Name _ Env -> (smt.error "duplicate declaration" Name) where (not (= false (smt.lookup Name Env)))
  C Name Bool Env -> [[Name [bool (smt.fresh C)]] | Env] where (= Bool (intern "Bool"))
  C Name [Underscore BitVec W] Env -> [[Name (smt.bv (smt.new-bits C (smt.width W)))] | Env]
    where (and (= Underscore (intern "_")) (= BitVec (intern "BitVec")))
  _ _ Sort _ -> (smt.error "unsupported sort" Sort))

(define smt.bool
  [bool L] -> L
  X -> (smt.error "expected Boolean term" X))

(define smt.bv-bits
  [bv | Bits] -> Bits
  X -> (smt.error "expected bit-vector term" X))

(define smt.same-sort
  [Sort | A] [Sort | B] -> true where (= (length A) (length B))
  A B -> (smt.error "incompatible sorts" [A B]))

(define smt.equality
  C [A B] -> (do (smt.same-sort A B)
    (smt.and-all C (smt.bitwise (/. X Y (smt.neg (smt.xor C X Y))) (tl A) (tl B)))))

(define smt.adjacent-equalities
  _ [_] -> []
  C [A B | Rest] -> [(smt.equality C [A B]) | (smt.adjacent-equalities C [B | Rest])])

(define smt.distinct-pairs
  _ [_] -> []
  C [A | Rest] ->
    (append (map (/. B (smt.neg (smt.equality C [A B]))) Rest)
            (smt.distinct-pairs C Rest)))

(define smt.boolean-fold
  _ F Init [] -> Init
  C F Init [X | Xs] -> (smt.boolean-fold C F (F C Init (smt.bool X)) Xs))

(define smt.implies
  _ [X] -> (smt.bool X)
  C [X | Xs] -> (smt.or C (smt.neg (smt.bool X)) (smt.implies C Xs)))

(define smt.bv-op
  C bvadd A B -> [bv | (smt.add C A B -1)]
  C bvsub A B -> [bv | (smt.add C A (map (/. L (smt.neg L)) B) 1)]
  C bvand A B -> [bv | (smt.bitwise (/. X Y (smt.and C X Y)) A B)]
  C bvor A B -> [bv | (smt.bitwise (/. X Y (smt.or C X Y)) A B)]
  C bvxor A B -> [bv | (smt.bitwise (/. X Y (smt.xor C X Y)) A B)]
  C bvult A B -> [bool (smt.ult C A B -1)]
  C bvugt A B -> [bool (smt.ult C B A -1)]
  C bvule A B -> [bool (smt.neg (smt.ult C B A -1))]
  C bvuge A B -> [bool (smt.neg (smt.ult C A B -1))]
  _ Op _ _ -> (smt.error "unsupported bit-vector operation" Op))

(define smt.apply
  _ not [X] -> [bool (smt.neg (smt.bool X))]
  C and Xs -> [bool (smt.boolean-fold C (fn smt.and) 1 Xs)]
  C or Xs -> [bool (smt.boolean-fold C (fn smt.or) -1 Xs)]
  C xor [A B | Rest] -> [bool (smt.boolean-fold C (fn smt.xor) -1 [A B | Rest])]
  C => [A B | Rest] -> [bool (smt.implies C [A B | Rest])]
  C = [A B | Rest] -> [bool (smt.and-all C (smt.adjacent-equalities C [A B | Rest]))]
  C distinct [A B | Rest] -> [bool (smt.and-all C (smt.distinct-pairs C [A B | Rest]))]
  C ite [Test A B] -> (do (smt.same-sort A B)
    (let L (smt.bool Test)
      [(hd A) | (smt.bitwise (/. X Y (smt.ite-bit C L X Y)) (tl A) (tl B))]))
  _ bvnot [A] -> [bv | (map (/. L (smt.neg L)) (smt.bv-bits A))]
  C bvneg [A] -> (let Bits (smt.bv-bits A)
    [bv | (smt.add C (map (/. L (smt.neg L)) Bits) (map (/. Ignored -1) Bits) 1)])
  _ concat [A B] -> (smt.bv (append (smt.bv-bits B) (smt.bv-bits A)))
  C Op [A B] -> (do (smt.same-sort A B)
    (smt.bv-op C Op (smt.bv-bits A) (smt.bv-bits B)))
  _ Op _ -> (smt.error "unsupported operation or wrong arity" Op))

(define smt.parse-indexed
  ["b" "v" D | Ds] W -> (smt.bv (smt.decimal-bits (map (fn smt.digit) [D | Ds]) (smt.width W)))
  Name _ -> (smt.error "unsupported indexed literal" Name))

(define smt.encode
  _ _ true -> [bool 1]
  _ _ false -> [bool -1]
  _ _ [Head Name W] -> (smt.parse-indexed (explode (str Name)) W) where (= Head (intern "_"))
  C Env [Op | Args] -> (smt.apply C Op (map (/. Arg (smt.encode C Env Arg)) Args))
  _ Env Name -> (let Binding (smt.lookup Name Env) Parsed (smt.literal (explode (str Name)))
    (if (not (= false Binding)) Binding (if (not (= false Parsed)) Parsed (smt.error "unknown term" Name)))))

(define smt.term-text
  [] -> "()"
  [X | Xs] -> (cn "(" (cn (smt.term-text X) (cn (smt.tail-text Xs) ")")))
  X -> (str X))

(define smt.tail-text
  [] -> ""
  [X | Xs] -> (cn " " (cn (smt.term-text X) (smt.tail-text Xs))))

(define smt.value-text
  S [bool L] -> (if (= 1 (smt.value S L)) "true" "false")
  S [bv | Bits] -> (cn "#b" (smt.bit-text S (reverse Bits))))

(define smt.show-values
  _ _ [] -> ok
  Env S [Name | Names] ->
    (let Term (smt.lookup Name Env)
      (if (not (= false Term))
          (do (pr (cn (cn "(" (smt.term-text Name)) (cn " " (cn (smt.value-text S Term) ")"))))
              (if (empty? Names) ok (pr " "))
              (smt.show-values Env S Names))
          (smt.error "get-value expects a declared constant" Name))))

(define smt.commands
  _ _ _ [] -> ok
  _ _ _ [[reset] | Rest] -> (smt.commands (smt.new-cnf) [] false Rest)
  C Env S [[set-logic Logic] | Rest] -> (smt.commands C Env S Rest)
    where (= Logic (intern "QF_BV"))
  C Env S [[set-option Colon produce-models true] | Rest] -> (smt.commands C Env S Rest)
    where (= Colon (intern ":"))
  C Env _ [[declare-const Name Sort] | Rest] ->
    (smt.commands C (smt.make-binding C Name Sort Env) false Rest)
      where (smt.var-name? Name)
  C Env _ [[declare-fun Name [] Sort] | Rest] ->
    (smt.commands C (smt.make-binding C Name Sort Env) false Rest)
      where (smt.var-name? Name)
  C Env _ [[assert Term] | Rest] ->
    (do (smt.emit C [(smt.bool (smt.encode C Env Term))])
        (smt.commands C Env false Rest))
  C Env _ [[check-sat] | Rest] ->
    (let Answer (smt.solve C)
      (do (output "~A~%" (if (fst Answer) sat unsat))
          (smt.commands C Env (if (fst Answer) (snd Answer) false) Rest)))
  C Env S [[get-value Names] | Rest] ->
    (if (not (= false S)) (do (pr "(") (smt.show-values Env S Names) (output ")~%")
              (smt.commands C Env S Rest))
          (simple-error "get-value requires a preceding sat result"))
  _ _ _ [[exit] | _] -> ok
  _ _ _ [Command | _] -> (smt.error "unsupported command" Command))

(define smt.run
  Source -> (let Forms (read-from-string-unprocessed (smt.strip-comments Source))
    (smt.commands (smt.new-cnf) [] false Forms)))

(define smt.run-file
  [_ Path] -> (smt.run (read-file-as-string Path))
  _ -> (simple-error "provide one SMT-LIB input file"))

(define smt.main
  -> (smt.run-file (value *argv*)))
