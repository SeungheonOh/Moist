namespace Moist.Plutus

@[irreducible] def uplcIntegerTDiv (a b : Int) : Int :=
  a.tdiv b

@[irreducible] def uplcIntegerTMod (a b : Int) : Int :=
  a.tmod b

@[irreducible] def uplcIntegerDiv (a b : Int) : Int :=
  let q := uplcIntegerTDiv a b
  let r := uplcIntegerTMod a b
  if r == 0 || ((a >= 0) == (b >= 0)) then q else q - 1

@[irreducible] def uplcIntegerMod (a b : Int) : Int :=
  a - b * uplcIntegerDiv a b

end Moist.Plutus
