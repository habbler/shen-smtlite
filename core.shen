\\ Signed literals identify Boolean variables. Variable 1 is fixed true.
(defstruct smt.cnf
  (mutable count : number)
  (mutable clauses : (list (list number))))

(define smt.new-cnf {--> smt.cnf}
  -> (smt.cnf.make 1 [[1]]))

(define smt.fresh {smt.cnf --> number}
  C -> (let N (+ 1 (smt.cnf.count C))
        (do (smt.cnf.count-> C N) N)))

(define smt.emit {smt.cnf --> (list number) --> symbol}
  C L -> (do (smt.cnf.clauses-> C [L | (smt.cnf.clauses C)]) ok))

(define smt.neg {number --> number}
  X -> (- 0 X))

(define smt.and {smt.cnf --> number --> number --> number}
  _ -1 _ -> -1
  _ _ -1 -> -1
  _ 1 B -> B
  _ A 1 -> A
  _ A A -> A
  _ A B -> -1 where (= A (smt.neg B))
  C A B -> (let X (smt.fresh C)
        NX (smt.neg X)
    (do (smt.emit C [NX A])
        (smt.emit C [NX B])
        (smt.emit C [X (smt.neg A) (smt.neg B)])
        X)))

(define smt.or {smt.cnf --> number --> number --> number}
  C A B -> (smt.neg (smt.and C (smt.neg A) (smt.neg B))))

(define smt.xor {smt.cnf --> number --> number --> number}
  _ -1 B -> B
  _ A -1 -> A
  _ 1 B -> (smt.neg B)
  _ A 1 -> (smt.neg A)
  _ A A -> -1
  _ A B -> 1 where (= A (smt.neg B))
  C A B -> (let X (smt.fresh C)
        NA (smt.neg A) NB (smt.neg B) NX (smt.neg X)
    (do (smt.emit C [NA NB NX]) (smt.emit C [A B NX])
        (smt.emit C [NA B X]) (smt.emit C [A NB X]) X)))

(define smt.and-all {smt.cnf --> (list number) --> number}
  _ [] -> 1
  C [X | Xs] -> (smt.and C X (smt.and-all C Xs)))

(define smt.new-bits {smt.cnf --> number --> (list number)}
  _ 0 -> []
  C N -> [(smt.fresh C) | (smt.new-bits C (- N 1))])

(define smt.bitwise {(number --> number --> number) --> (list number) --> (list number) --> (list number)}
  _ [] [] -> []
  F [A | As] [B | Bs] -> [(F A B) | (smt.bitwise F As Bs)])

(define smt.add {smt.cnf --> (list number) --> (list number) --> number --> (list number)}
  _ [] [] _ -> []
  C [A | As] [B | Bs] Carry ->
    (let Either (smt.xor C A B)
         Sum (smt.xor C Either Carry)
         Next (smt.or C (smt.and C A B) (smt.and C Either Carry))
      [Sum | (smt.add C As Bs Next)]))

(define smt.ult {smt.cnf --> (list number) --> (list number) --> number --> number}
  _ [] [] Less -> Less
  C [A | As] [B | Bs] Less ->
    (let Here (smt.or C (smt.and C (smt.neg A) B)
                       (smt.and C (smt.neg (smt.xor C A B)) Less))
      (smt.ult C As Bs Here)))

\\ Watch lists are indexed by signed literal. Watches survive backtracking.
(defstruct smt.clause
  (mutable first : number)
  (mutable second : number)
  (mutable rest : (list number)))

(defstruct smt.state
  (count : number)
  (values : (vector number))
  (watches : (vector (list smt.clause)))
  (mutable trail : (list number))
  (mutable pending : (list number)))

(define smt.fill {(vector A) --> number --> A --> (vector A)}
  V 0 _ -> V
  V N X -> (do (vector-> V N X) (smt.fill V (- N 1) X)))

(define smt.new-state {number --> smt.state}
  N -> (let Slots (+ (* 2 N) 1)
     (smt.state.make N (smt.fill (vector N) N 0)
                      (smt.fill (vector Slots) Slots []) [] [])))

(define smt.var {number --> number}
  L -> (if (< L 0) (smt.neg L) L))

(define smt.index {number --> number}
  L -> (if (< L 0) (+ 1 (* 2 (smt.var L))) (* 2 L)))

(define smt.value {smt.state --> number --> number}
  S L -> (let V (<-vector (smt.state.values S) (smt.var L))
    (if (< L 0) (smt.neg V) V)))

(define smt.assign {smt.state --> number --> boolean}
  S L -> (let V (smt.value S L)
    (if (= V 1) true
        (if (= V -1) false
            (let Value (if (< L 0) -1 1)
              (do (vector-> (smt.state.values S) (smt.var L) Value)
                  (smt.state.trail-> S [L | (smt.state.trail S)])
                  (smt.state.pending-> S [L | (smt.state.pending S)])
                  true))))))

(define smt.watch {smt.state --> number --> smt.clause --> symbol}
  S L C -> (let W (smt.state.watches S) I (smt.index L)
    (do (vector-> W I [C | (<-vector W I)]) ok)))

(define smt.attach {smt.state --> (list (list number)) --> boolean}
  _ [] -> true
  _ [[] | _] -> false
  S [[L] | Cs] -> (and (smt.assign S L) (smt.attach S Cs))
  S [[A B | Ls] | Cs] ->
    (let C (smt.clause.make A B Ls)
      (do (smt.watch S A C) (smt.watch S B C) (smt.attach S Cs))))

(define smt.replacement {smt.state --> (list number) --> (number * (list number))}
  _ [] -> (@p 0 [])
  S [L | Ls] -> (@p L Ls) where (not (= -1 (smt.value S L)))
  S [L | Ls] -> (let Result (smt.replacement S Ls)
                  (@p (fst Result) [L | (snd Result)])))

(define smt.other {smt.clause --> number --> number}
  C L -> (if (= L (smt.clause.first C)) (smt.clause.second C) (smt.clause.first C)))

(define smt.move-watch {smt.clause --> number --> number --> (list number) --> symbol}
  C Old New Rest ->
    (do (if (= Old (smt.clause.first C)) (smt.clause.first-> C New) (smt.clause.second-> C New))
        (smt.clause.rest-> C [Old | Rest])
        ok))

\\ The current watch bucket is detached during propagation. Restore its tail on conflict.
(define smt.keep-unprocessed {smt.state --> number --> (list smt.clause) --> boolean}
  S L Cs -> (let W (smt.state.watches S) I (smt.index L)
    (do (vector-> W I (append Cs (<-vector W I))) false)))

(define smt.rewatch {smt.state --> number --> (list smt.clause) --> boolean}
  _ _ [] -> true
  S L [C | Cs] ->
    (let Other (smt.other C L)
      (if (= 1 (smt.value S Other))
          (do (smt.watch S L C) (smt.rewatch S L Cs))
          (let Result (smt.replacement S (smt.clause.rest C))
               Pick (fst Result)
            (if (= 0 Pick)
                (do (smt.watch S L C)
                    (if (smt.assign S Other)
                        (smt.rewatch S L Cs)
                        (smt.keep-unprocessed S L Cs)))
                (do (smt.move-watch C L Pick (snd Result))
                    (smt.watch S Pick C)
                    (smt.rewatch S L Cs)))))))

(define smt.propagate-next {smt.state --> (list number) --> boolean}
  _ [] -> true
  S [L | Ls] ->
    (let FalseLit (smt.neg L) W (smt.state.watches S)
         I (smt.index FalseLit) Cs (<-vector W I)
      (do (smt.state.pending-> S Ls) (vector-> W I [])
          (and (smt.rewatch S FalseLit Cs)
               (smt.propagate-next S (smt.state.pending S))))))

(define smt.rollback {smt.state --> (list number) --> (list number) --> symbol}
  S Mark Mark -> (do (smt.state.trail-> S Mark) (smt.state.pending-> S []) ok)
  S Mark [L | Ls] ->
    (do (vector-> (smt.state.values S) (smt.var L) 0)
        (smt.rollback S Mark Ls)))

(define smt.next {smt.state --> number --> number}
  S N -> 0 where (> N (smt.state.count S))
  S N -> N where (= 0 (smt.value S N))
  S N -> (smt.next S (+ 1 N)))

(define smt.search {smt.state --> boolean}
  S -> (and (smt.propagate-next S (smt.state.pending S))
            (let N (smt.next S 1) Mark (smt.state.trail S)
              (if (= N 0) true
                  (if (and (smt.assign S N) (smt.search S)) true
                      (do (smt.rollback S Mark (smt.state.trail S))
                          (and (smt.assign S (smt.neg N)) (smt.search S))))))))

(define smt.solve {smt.cnf --> (boolean * smt.state)}
  C -> (let S (smt.new-state (smt.cnf.count C))
     (@p (and (smt.attach S (reverse (smt.cnf.clauses C))) (smt.search S)) S)))

(define smt.error {string --> A --> B}
  Message Form -> (simple-error (make-string "~A: ~S" Message Form)))

(define smt.number-bits {number --> number --> (list number)}
  _ 0 -> []
  N W -> [(if (= 0 (mod N 2)) -1 1) | (smt.number-bits (floor (/ N 2)) (- W 1))])

(define smt.bit-char {string --> number}
  "0" -> -1
  "1" -> 1
  C -> (smt.error "bad binary digit" C))

(define smt.hex-char {string --> number}
  C -> (let N (string->n C)
    (if (and (>= N 48) (<= N 57)) (- N 48)
      (if (and (>= N 65) (<= N 70)) (- N 55)
        (if (and (>= N 97) (<= N 102)) (- N 87)
          (smt.error "bad hex digit" C))))))

(define smt.hex-bits {(list string) --> (list number)}
  [] -> []
  [C | Cs] -> (append (smt.number-bits (smt.hex-char C) 4) (smt.hex-bits Cs)))

(define smt.digit {string --> number}
  C -> (let D (- (string->n C) 48)
    (if (and (>= D 0) (<= D 9)) D (smt.error "bad decimal digit" C))))

(define smt.halve {(list number) --> number --> ((list number) * number)}
  [] Carry -> (@p [] Carry)
  [D | Ds] Carry -> (let Value (+ (* 10 Carry) D)
      Tail (smt.halve Ds (mod Value 2))
    (@p [(floor (/ Value 2)) | (fst Tail)] (snd Tail))))

(define smt.decimal-bits {(list number) --> number --> (list number)}
  _ 0 -> []
  Digits W -> (let Half (smt.halve Digits 0)
    [(if (= 0 (snd Half)) -1 1) | (smt.decimal-bits (fst Half) (- W 1))]))


(define smt.width {number --> number}
  W -> W where (and (integer? W) (> W 0) (<= W 64))
  W -> (smt.error "supported bit widths are 1 through 64" W))

(define smt.ite-bit {smt.cnf --> number --> number --> number --> number}
  C Test A B -> (smt.or C (smt.and C Test A) (smt.and C (smt.neg Test) B)))

(define smt.bit-text {smt.state --> (list number) --> string}
  _ [] -> ""
  S [L | Ls] -> (cn (if (= 1 (smt.value S L)) "1" "0") (smt.bit-text S Ls)))

\\ Blank SMT-LIB comments in place so large source files need only one copy.
(define smt.blank-comments {buffer.view --> fixnum --> fixnum --> boolean --> buffer.view}
  View End End _ -> View
  View At End Comment ->
    (let Byte (buffer.u8 View At)
      (if (or (fx= Byte 10) (fx= Byte 13))
          (smt.blank-comments View (fx+ At 1) End false)
          (if (or Comment (fx= Byte 59))
              (smt.blank-comments (buffer.u8-> View At 32) (fx+ At 1) End true)
              (smt.blank-comments View (fx+ At 1) End false)))))

(define smt.strip-comments {string --> string}
  Source -> (let View (buffer.from-string Source)
    (buffer.string (smt.blank-comments View 0 (buffer.length View) false))))
