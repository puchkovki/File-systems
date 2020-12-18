-------------------------------- MODULE crossing --------------------------------
EXTENDS TLC

(* --algorithm cross
variables i \in {9,5,3,1}, states = {};
begin
A:
  if s = 0 then
    print states;
    print ("END");
  elsif s % 2 then
      if (s+i ~\in {1,5,6,9,10,14}) /\ (if s+i <= 15) /\ (s+i ~\in states) then
          states := states \cup {s+i};
          goto A;
      end if;
  else
      if (s-i ~\in {1,5,6,9,10,14}) /\ (if s+i >= 0) /\ (s-i ~\in states) then
          states := states \cup {s-i};
          goto A;
      end if;
  end if;
end algorithm; *)
=============================================================================