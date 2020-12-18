-------------------------------- MODULE crossing --------------------------------
EXTENDS TLC, Sequences, Integers

(* --algorithm cross
variable states = <<>>, k = 0, s = 0, 
define 
  D == DOMAIN states
end define;
begin
A:
  s := Tail(states);
  if s = 0 then
    print states;
    print ("END");
  elsif s % 2 = 0 then
      with i \in {9,5,3,1} do
        if (s+i \notin {1,5,6,9,10,14}) /\ (s+i <= 15) /\ (s+i \notin states) then
            k := s+i;
            states := Append(states, k);
            goto A;
        end if;
      end with;
  else
      with i \in {9,5,3,1} do
        if (s-i \notin {1,5,6,9,10,14}) /\ (s+i >= 0) /\ (s-i \notin states) then
            k := s-i;
            states := Append(states, k);
            goto A;
        end if;
      end with;
  end if;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a552e52972571a12f9b9fba3afbcff80
VARIABLES states, k, s, pc

(* define statement *)
D == DOMAIN states


vars == << states, k, s, pc >>

Init == (* Global variables *)
        /\ states = <<>>
        /\ k = 0
        /\ s = 0
        /\ pc = "A"

A == /\ pc = "A"
     /\ s' = Tail(states)
     /\ IF s' = 0
           THEN /\ PrintT(states)
                /\ PrintT(("END"))
                /\ pc' = "Done"
                /\ UNCHANGED << states, k >>
           ELSE /\ IF s' % 2 = 0
                      THEN /\ \E i \in {9,5,3,1}:
                                IF (s'+i \notin {1,5,6,9,10,14}) /\ (s'+i <= 15) /\ (s'+i \notin states)
                                   THEN /\ k' = s'+i
                                        /\ states' = Append(states, k')
                                        /\ pc' = "A"
                                   ELSE /\ pc' = "Done"
                                        /\ UNCHANGED << states, k >>
                      ELSE /\ \E i \in {9,5,3,1}:
                                IF (s'-i \notin {1,5,6,9,10,14}) /\ (s'+i >= 0) /\ (s'-i \notin states)
                                   THEN /\ k' = s'-i
                                        /\ states' = Append(states, k')
                                        /\ pc' = "A"
                                   ELSE /\ pc' = "Done"
                                        /\ UNCHANGED << states, k >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c37f3c48cef1914730707f0d06eef661
=============================================================================
