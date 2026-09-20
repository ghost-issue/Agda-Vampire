; SMTLIB

(declare-sort vec.V 0) 
(declare-fun vec._+_ (vec.V vec.V) vec.V) 
(declare-fun vec.-_ (vec.V) vec.V) 
(declare-const vec.ze vec.V) 
(assert (! (forall ((u vec.V)) (= (vec._+_ (vec.ze ) u) u)) :named vec.neutl)) 
(assert (! (forall ((u vec.V)) (= (vec._+_ (vec.-_ u) u) (vec.ze ))) :named vec.negl)) 
(assert (! (forall ((u vec.V) (v vec.V) (w vec.V))  (= (vec._+_ (vec._+_ u v) w) (vec._+_ u (vec._+_ v w)))) :named vec.assoc)) 
(declare-const u vec.V) 
(declare-const v vec.V) 
(assert (! (forall () (= (vec._+_ u v) v)) :named e)) 
(assert-not (! (= u (vec.ze )) :named vec.ze-uniq))