\\ Signed literals identify Boolean variables. Variable 1 is fixed true.
(defstruct smt.cnf
  (mutable count : fixnum)
  (mutable clauses : (list (list fixnum))))

(define smt.new-cnf {--> smt.cnf}
  -> (smt.cnf.make 1 [[1]]))

(define smt.fresh {smt.cnf --> fixnum}
  C -> (let N (fx+ 1 (smt.cnf.count C))
        (do (smt.cnf.count-> C N) N)))

(define smt.emit {smt.cnf --> (list fixnum) --> symbol}
  C L -> (do (smt.cnf.clauses-> C [L | (smt.cnf.clauses C)]) ok))

(define smt.neg {fixnum --> fixnum}
  X -> (fx- 0 X))

(define smt.and {smt.cnf --> fixnum --> fixnum --> fixnum}
  _ -1 _ -> -1
  _ _ -1 -> -1
  _ 1 B -> B
  _ A 1 -> A
  _ A A -> A
  _ A B -> -1 where (fx= A (smt.neg B))
  C A B -> (let X (smt.fresh C)
        NX (smt.neg X)
    (do (smt.emit C [NX A])
        (smt.emit C [NX B])
        (smt.emit C [X (smt.neg A) (smt.neg B)])
        X)))

(define smt.or {smt.cnf --> fixnum --> fixnum --> fixnum}
  C A B -> (smt.neg (smt.and C (smt.neg A) (smt.neg B))))

(define smt.xor {smt.cnf --> fixnum --> fixnum --> fixnum}
  _ -1 B -> B
  _ A -1 -> A
  _ 1 B -> (smt.neg B)
  _ A 1 -> (smt.neg A)
  _ A A -> -1
  _ A B -> 1 where (fx= A (smt.neg B))
  C A B -> (let X (smt.fresh C)
        NA (smt.neg A) NB (smt.neg B) NX (smt.neg X)
    (do (smt.emit C [NA NB NX]) (smt.emit C [A B NX])
        (smt.emit C [NA B X]) (smt.emit C [A NB X]) X)))

(define smt.and-all {smt.cnf --> (list fixnum) --> fixnum}
  _ [] -> 1
  C [X | Xs] -> (smt.and C X (smt.and-all C Xs)))

(define smt.new-bits {smt.cnf --> fixnum --> (list fixnum)}
  _ 0 -> []
  C N -> [(smt.fresh C) | (smt.new-bits C (fx- N 1))])

(define smt.bitwise {(fixnum --> fixnum --> fixnum) --> (list fixnum) --> (list fixnum) --> (list fixnum)}
  _ [] [] -> []
  F [A | As] [B | Bs] -> [(F A B) | (smt.bitwise F As Bs)])

(define smt.add {smt.cnf --> (list fixnum) --> (list fixnum) --> fixnum --> (list fixnum)}
  _ [] [] _ -> []
  C [A | As] [B | Bs] Carry ->
    (let Either (smt.xor C A B)
         Sum (smt.xor C Either Carry)
         Next (smt.or C (smt.and C A B) (smt.and C Either Carry))
      [Sum | (smt.add C As Bs Next)]))

(define smt.ult {smt.cnf --> (list fixnum) --> (list fixnum) --> fixnum --> fixnum}
  _ [] [] Less -> Less
  C [A | As] [B | Bs] Less ->
    (let Here (smt.or C (smt.and C (smt.neg A) B)
                       (smt.and C (smt.neg (smt.xor C A B)) Less))
      (smt.ult C As Bs Here)))

\\ Watch lists are indexed by signed literal. Watches survive backtracking.
(defstruct smt.clause
  (mutable first : fixnum)
  (mutable second : fixnum)
  (mutable rest : (list fixnum)))

(defstruct smt.state
  (count : fixnum)
  (values : (vector fixnum))
  (watches : (vector (list smt.clause)))
  (mutable trail : (list fixnum))
  (mutable pending : (list fixnum)))

(define smt.fill {(vector A) --> fixnum --> A --> (vector A)}
  V 0 _ -> V
  V N X -> (do (fxvector-> V N X) (smt.fill V (fx- N 1) X)))

(define smt.new-state {fixnum --> smt.state}
  N -> (let Slots (fx+ (fx* 2 N) 1)
     (smt.state.make N (smt.fill (vector (fx->number N)) N 0)
                      (smt.fill (vector (fx->number Slots)) Slots []) [] [])))

(define smt.var {fixnum --> fixnum}
  L -> (if (fx< L 0) (smt.neg L) L))

(define smt.index {fixnum --> fixnum}
  L -> (if (fx< L 0) (fx+ 1 (fx* 2 (smt.var L))) (fx* 2 L)))

(define smt.value {smt.state --> fixnum --> fixnum}
  S L -> (let V (fx<-vector (smt.state.values S) (smt.var L))
    (if (fx< L 0) (smt.neg V) V)))

(define smt.assign {smt.state --> fixnum --> boolean}
  S L -> (let V (smt.value S L)
    (if (fx= V 1) true
        (if (fx= V -1) false
            (let Value (type (if (fx< L 0) -1 1) fixnum)
              (do (fxvector-> (smt.state.values S) (smt.var L) Value)
                  (smt.state.trail-> S [L | (smt.state.trail S)])
                  (smt.state.pending-> S [L | (smt.state.pending S)])
                  true))))))

(define smt.watch {smt.state --> fixnum --> smt.clause --> symbol}
  S L C -> (let W (smt.state.watches S) I (smt.index L)
    (do (fxvector-> W I [C | (fx<-vector W I)]) ok)))

(define smt.attach {smt.state --> (list (list fixnum)) --> boolean}
  _ [] -> true
  _ [[] | _] -> false
  S [[L] | Cs] -> (and (smt.assign S L) (smt.attach S Cs))
  S [[A B | Ls] | Cs] ->
    (let C (smt.clause.make A B Ls)
      (do (smt.watch S A C) (smt.watch S B C) (smt.attach S Cs))))

(define smt.replacement {smt.state --> (list fixnum) --> (fixnum * (list fixnum))}
  _ [] -> (@p 0 [])
  S [L | Ls] -> (@p L Ls) where (not (fx= -1 (smt.value S L)))
  S [L | Ls] -> (let Result (smt.replacement S Ls)
                  (@p (fst Result) [L | (snd Result)])))

(define smt.other {smt.clause --> fixnum --> fixnum}
  C L -> (if (fx= L (smt.clause.first C)) (smt.clause.second C) (smt.clause.first C)))

(define smt.move-watch {smt.clause --> fixnum --> fixnum --> (list fixnum) --> symbol}
  C Old New Rest ->
    (do (if (fx= Old (smt.clause.first C)) (smt.clause.first-> C New) (smt.clause.second-> C New))
        (smt.clause.rest-> C [Old | Rest])
        ok))

\\ The current watch bucket is detached during propagation. Restore its tail on conflict.
(define smt.keep-unprocessed {smt.state --> fixnum --> (list smt.clause) --> boolean}
  S L Cs -> (let W (smt.state.watches S) I (smt.index L)
    (do (fxvector-> W I (append Cs (fx<-vector W I))) false)))

(define smt.rewatch {smt.state --> fixnum --> (list smt.clause) --> boolean}
  _ _ [] -> true
  S L [C | Cs] ->
    (let Other (smt.other C L)
      (if (fx= 1 (smt.value S Other))
          (do (smt.watch S L C) (smt.rewatch S L Cs))
          (let Result (smt.replacement S (smt.clause.rest C))
               Pick (fst Result)
            (if (fx= 0 Pick)
                (do (smt.watch S L C)
                    (if (smt.assign S Other)
                        (smt.rewatch S L Cs)
                        (smt.keep-unprocessed S L Cs)))
                (do (smt.move-watch C L Pick (snd Result))
                    (smt.watch S Pick C)
                    (smt.rewatch S L Cs)))))))

(define smt.propagate-next {smt.state --> (list fixnum) --> boolean}
  _ [] -> true
  S [L | Ls] ->
    (let FalseLit (smt.neg L) W (smt.state.watches S)
         I (smt.index FalseLit) Cs (fx<-vector W I)
      (do (smt.state.pending-> S Ls) (fxvector-> W I [])
          (and (smt.rewatch S FalseLit Cs)
               (smt.propagate-next S (smt.state.pending S))))))

(define smt.rollback {smt.state --> (list fixnum) --> (list fixnum) --> symbol}
  S Mark Mark -> (do (smt.state.trail-> S Mark) (smt.state.pending-> S []) ok)
  S Mark [L | Ls] ->
    (do (fxvector-> (smt.state.values S) (smt.var L) 0)
        (smt.rollback S Mark Ls)))

(define smt.next {smt.state --> fixnum --> fixnum}
  S N -> 0 where (fx> N (smt.state.count S))
  S N -> N where (fx= 0 (smt.value S N))
  S N -> (smt.next S (fx+ 1 N)))

(define smt.search {smt.state --> boolean}
  S -> (and (smt.propagate-next S (smt.state.pending S))
            (let N (smt.next S 1) Mark (smt.state.trail S)
              (if (fx= N 0) true
                  (if (and (smt.assign S N) (smt.search S)) true
                      (do (smt.rollback S Mark (smt.state.trail S))
                          (and (smt.assign S (smt.neg N)) (smt.search S))))))))

(define smt.solve {smt.cnf --> (boolean * smt.state)}
  C -> (let S (smt.new-state (smt.cnf.count C))
     (@p (and (smt.attach S (reverse (smt.cnf.clauses C))) (smt.search S)) S)))

(define smt.error {string --> A --> B}
  Message Form -> (simple-error (make-string "~A: ~S" Message Form)))

(define smt.number-bits {fixnum --> fixnum --> (list fixnum)}
  _ 0 -> []
  N W -> [(if (fx= 0 (fxremainder N 2)) -1 1) | (smt.number-bits (fxquotient N 2) (fx- W 1))])

(define smt.bit-char {string --> fixnum}
  "0" -> -1
  "1" -> 1
  C -> (smt.error "bad binary digit" C))

(define smt.hex-char {string --> fixnum}
  C -> (let N (fixnum (string->n C))
    (if (and (fx>= N 48) (fx<= N 57)) (fx- N 48)
      (if (and (fx>= N 65) (fx<= N 70)) (fx- N 55)
        (if (and (fx>= N 97) (fx<= N 102)) (fx- N 87)
          (smt.error "bad hex digit" C))))))

(define smt.hex-bits {(list string) --> (list fixnum)}
  [] -> []
  [C | Cs] -> (append (smt.number-bits (smt.hex-char C) 4) (smt.hex-bits Cs)))

(define smt.digit {string --> fixnum}
  C -> (let D (fx- (fixnum (string->n C)) 48)
    (if (and (fx>= D 0) (fx<= D 9)) D (smt.error "bad decimal digit" C))))

(define smt.halve {(list fixnum) --> fixnum --> ((list fixnum) * fixnum)}
  [] Carry -> (@p [] Carry)
  [D | Ds] Carry -> (let Value (fx+ (fx* 10 Carry) D)
      Tail (smt.halve Ds (fxremainder Value 2))
    (@p [(fxquotient Value 2) | (fst Tail)] (snd Tail))))

(define smt.decimal-bits {(list fixnum) --> fixnum --> (list fixnum)}
  _ 0 -> []
  Digits W -> (let Half (smt.halve Digits 0)
    [(if (fx= 0 (snd Half)) -1 1) | (smt.decimal-bits (fst Half) (fx- W 1))]))

(define smt.width {number --> fixnum}
  W -> (fixnum W) where (and (integer? W) (> W 0) (<= W 64))
  W -> (smt.error "supported bit widths are 1 through 64" W))

(define smt.ite-bit {smt.cnf --> fixnum --> fixnum --> fixnum --> fixnum}
  C Test A B -> (smt.or C (smt.and C Test A) (smt.and C (smt.neg Test) B)))

(define smt.bit-text {smt.state --> (list fixnum) --> string}
  _ [] -> ""
  S [L | Ls] -> (cn (if (fx= 1 (smt.value S L)) "1" "0") (smt.bit-text S Ls)))

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
