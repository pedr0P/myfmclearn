/- variable (a b c x y z : Int) -/

axiom Z_Refl : ∀ (a : Int), a = a
axiom Z_Symm : ∀ (a b : Int), a = b → b = a
axiom Z_Trans : ∀ (a b c : Int), a = b ∧ b = c → a = c

axiom ZA_Ass : ∀ (x y z : Int), x + y + z = x + (y + z)
axiom ZA_Com : ∀ (x y : Int), x + y = y + x
axiom ZA_IdR : ∀ (x : Int), x + 0 = x
axiom ZA_InvR : ∀ (x : Int), x + (-x) = 0

axiom ZAM_DistR : ∀ (x y d : Int), (x + y) * d = x * d + y * d

axiom ZM_Ass : ∀ (x y z : Int), x * y * z = x * (y * z)
axiom ZM_Com : ∀ (x y : Int), x * y = x * y
axiom ZM_idR : ∀ (x : Int), x * 0 = 0
