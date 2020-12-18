-------------------------------- MODULE crossing --------------------------------
EXTENDS TLC, Sequences, Integers

(* --algorithm cross
variable states = {}, k = 0, s, tower = <<<<1, 2, 3>>, <<>>, <<>>>>, 
define 
  D == DOMAIN tower
end define;
begin
A:
  if s = 0 then
    print states;
    print ("END");
  elsif s % 2 = 0 then
      with i \in {9,5,3,1} do
        if (s+i \notin {1,5,6,9,10,14}) /\ (s+i <= 15) /\ (s+i \notin states) then
            k := s+i;
            states := states \cup {k};
            goto A;
        end if;
      end with;
  else
      with i \in {9,5,3,1} do
        if (s-i \notin {1,5,6,9,10,14}) /\ (s+i >= 0) /\ (s-i \notin states) then
            k := s-i;
            states := states \cup {k};
            goto A;
        end if;
      end with;
  end if;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-283f9b371bcd7f8d3375802dd715e78e
CONSTANT defaultInitValue
VARIABLES states, k, s, tower, pc

(* define statement *)
D == DOMAIN tower


vars == << states, k, s, tower, pc >>

Init == (* Global variables *)
        /\ states = {}
        /\ k = 0
        /\ s = defaultInitValue
        /\ tower = <<<<1, 2, 3>>, <<>>, <<>>>>
        /\ pc = "A"

A == /\ pc = "A"
     /\ IF s = 0
           THEN /\ PrintT(states)
                /\ PrintT(("END"))
                /\ pc' = "Done"
                /\ UNCHANGED << states, k >>
           ELSE /\ IF s % 2 = 0
                      THEN /\ \E i \in {9,5,3,1}:
                                IF (s+i \notin {1,5,6,9,10,14}) /\ (s+i <= 15) /\ (s+i \notin states)
                                   THEN /\ k' = s+i
                                        /\ states' = (states \cup {k'})
                                        /\ pc' = "A"
                                   ELSE /\ pc' = "Done"
                                        /\ UNCHANGED << states, k >>
                      ELSE /\ \E i \in {9,5,3,1}:
                                IF (s-i \notin {1,5,6,9,10,14}) /\ (s+i >= 0) /\ (s-i \notin states)
                                   THEN /\ k' = s-i
                                        /\ states' = (states \cup {k'})
                                        /\ pc' = "A"
                                   ELSE /\ pc' = "Done"
                                        /\ UNCHANGED << states, k >>
     /\ UNCHANGED << s, tower >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-52aba6d6e827d929ee37b907352af822
=============================================================================
