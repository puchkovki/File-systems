-------------------------------- MODULE crossing --------------------------------
EXTENDS TLC, Integers, FiniteSets

(* --algorithm cross
\* Берега: изначально на одной все объекты, а на другой пусто
variables coast = <<{"W", "G", "C", "H"}, {} >>

define 
  C == DOMAIN coast
end define;

begin
while TRUE do
    \* Решение найдено, когда на второй берег реки перебрались все объекты
    assert coast[2] /= {"W", "G", "C", "H"};
    \* Берег на который перевозим объект тот, на котором сейчас нет перевозчика "Н"
    with side \in {x \in C: "H" \in coast[x]},
         \* С того же берега и берем объект для перевозки
         cargo \in coast[side] do
        \* Условия на перевозку: на берегу может остаться либо только волк с капустой ("W" & "C"),
        if coast[side] \ {cargo, "H"} = {"W", "C"} \/
          \* либо 1 любой объект
          Cardinality(coast[side] \ {cargo, "H"}) < 2 then
            \* Выбранный объект переходит с перевозчиком на другую сторону реки
            coast[side] := coast[side] \ {cargo, "H"} ||
            coast[CHOOSE to \in C \ {side} : TRUE] := UNION {coast[CHOOSE to \in C \ {side} : TRUE], {cargo, "H"}};
        end if;
     end with;
end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-baaabdd366cdc6f36dd0a032d5522190 (chksum(pcal) = "66221363" /\ chksum(tla) = "19de89c4") (chksum(pcal) = "66221363" /\ chksum(tla) = "19de89c4") (chksum(pcal) = "f3f91e83" /\ chksum(tla) = "e1530ad2") (chksum(pcal) = "195af298" /\ chksum(tla) = "8fe711ca") (chksum(pcal) = "fcd8264a" /\ chksum(tla) = "864425a0") (chksum(pcal) = "dfe6194f" /\ chksum(tla) = "3ff86bf3") (chksum(pcal) = "195af298" /\ chksum(tla) = "8fe711ca")
VARIABLE coast

(* define statement *)
C == DOMAIN coast


vars == << coast >>

Init == (* Global variables *)
        /\ coast = <<{"W", "G", "C", "H"}, {} >>

Next == /\ Assert(coast[2] /= {"W", "G", "C", "H"}, 
                  "Failure of assertion at line 15, column 5.")
        /\ \E side \in {x \in C: "H" \in coast[x]}:
             \E cargo \in coast[side]:
               IF  coast[side] \ {cargo, "H"} = {"W", "C"} \/
                  
                  Cardinality(coast[side] \ {cargo, "H"}) < 2
                  THEN /\ coast' = [coast EXCEPT ![side] = coast[side] \ {cargo, "H"},
                                                 ![CHOOSE to \in C \ {side} : TRUE] = UNION {coast[CHOOSE to \in C \ {side} : TRUE], {cargo, "H"}}]
                  ELSE /\ TRUE
                       /\ coast' = coast

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-52e19bd3274c2836a4ddcaf478251e0e
=============================================================================
