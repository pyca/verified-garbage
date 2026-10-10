import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Verified

/-! # Ed25519's point doubling and cached additions, in radix `2^64`, on x86-64 -/

namespace VG.Artifacts.Ed25519R64.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64.Point64
open VG.Impl.X25519.X86_64 (baseline adx)
open VG.Spec.Ed25519.Point64 (doubleExtApi addCachedExtApi addCachedProjApi addAffineExtApi doubleContract
  addCachedContract addAffineContract)

/-- How the functions work, with the field multiplications described by `mul`. -/
def notes (what mul : String) : List String := ["The function keeps `rbp` and `r12`–`r15` in `xmm0`–`xmm4` \
  while it runs, and runs " ++ what ++ " as `vg_ed25519_verify_equation` inlined it, with the \
  temporaries in slots 8–15: X25519's field operations on four 64-bit words, " ++ mul ++ ", folded \
  with `2^256 = 38`, and additions and subtractions, each folded once where an operand is a product."]

/-- The baseline's multiplications. -/
def baseMul : String := "multiplied with `mul` by rows (squares computing each cross product once)"

/-- BMI2 and ADX's multiplications. -/
def adxMul : String := "multiplied with BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once)"

/-- What the doubling runs. -/
def dblWhat : String :=
  "RFC 8032's doubling formula (§5.1.4), with `-E = 2XY` from one product and `F`, `G` and `H` \
    negated: eight products"

/-- What the additions run. -/
def addWhat (t : Bool) : String :=
  "RFC 8032's complete addition formula of the point in slots 4–7, cached, " ++
    (if t then "eight products" else "seven products, leaving out `T`'s")

/-- What the affine addition runs. -/
def affWhat : String :=
  "RFC 8032's complete addition formula of the point in slots 4–6, affine and cached, its `2Z` \
    `2` (so that `Z₁ · 2Z₂ = Z₁ + Z₁`): seven products"

/-- The affine addition's notes: `notes`, for the code of the comb's additions. -/
def affNotes (mul : String) : List String := ["The function keeps `rbp` and `r12`–`r15` in \
  `xmm0`–`xmm4` while it runs, and runs " ++ affWhat ++ ", as `vg_ed25519_scalar_base`'s comb \
  adds its table entries, with the temporaries in slots 8–15: X25519's field operations on four \
  64-bit words, " ++ mul ++ ", folded with `2^256 = 38`, and additions and subtractions, each \
  folded once where an operand is a product."]

theorem addAffine_verified : Verified X86_64.target (addAffineFn baseline)
    (addAffineContract X86_64.abi true) :=
  Verified.of_correct (addAffine_correct (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    addAffK_implies

theorem addAffineAdx_verified : Verified X86_64.target (addAffineFn adx)
    (addAffineContract X86_64.abi true) :=
  Verified.of_correct (addAffine_correct (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    addAffK_implies

theorem doubleExt_verified : Verified X86_64.target (doubleFn baseline true)
    (doubleContract X86_64.abi true) :=
  Verified.of_correct (double_correct true (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (doubleK_implies true)

theorem addExt_verified : Verified X86_64.target (addFn baseline true)
    (addCachedContract X86_64.abi true) :=
  Verified.of_correct (add_correct true (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies true)

theorem addProj_verified : Verified X86_64.target (addFn baseline false)
    (addCachedContract X86_64.abi false) :=
  Verified.of_correct (add_correct false (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies false)

theorem doubleExtAdx_verified : Verified X86_64.target (doubleFn adx true)
    (doubleContract X86_64.abi true) :=
  Verified.of_correct (double_correct true (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (doubleK_implies true)

theorem addExtAdx_verified : Verified X86_64.target (addFn adx true)
    (addCachedContract X86_64.abi true) :=
  Verified.of_correct (add_correct true (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies true)

theorem addProjAdx_verified : Verified X86_64.target (addFn adx false)
    (addCachedContract X86_64.abi false) :=
  Verified.of_correct (add_correct false (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies false)

def artifacts : List Artifact := [  { doubleExtApi with
    target := X86_64.target
    doc := doubleExtApi.doc (notes := (notes dblWhat baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·))
    code := doubleFn baseline true
    contract := doubleContract X86_64.abi true
    verified := doubleExt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addCachedExtApi with
    target := X86_64.target
    doc := addCachedExtApi.doc (notes := (notes (addWhat true) baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·))
    code := addFn baseline true
    contract := addCachedContract X86_64.abi true
    verified := addExt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addCachedProjApi with
    target := X86_64.target
    doc := addCachedProjApi.doc (notes := (notes (addWhat false) baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·))
    code := addFn baseline false
    contract := addCachedContract X86_64.abi false
    verified := addProj_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { doubleExtApi with
    target := X86_64.target
    name := doubleExtApi.name ++ "_adx"
    doc := doubleExtApi.doc (notes := (notes dblWhat adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·))
    code := doubleFn adx true
    contract := doubleContract X86_64.abi true
    verified := doubleExtAdx_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addCachedExtApi with
    target := X86_64.target
    name := addCachedExtApi.name ++ "_adx"
    doc := addCachedExtApi.doc (notes := (notes (addWhat true) adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·))
    code := addFn adx true
    contract := addCachedContract X86_64.abi true
    verified := addExtAdx_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addCachedProjApi with
    target := X86_64.target
    name := addCachedProjApi.name ++ "_adx"
    doc := addCachedProjApi.doc (notes := (notes (addWhat false) adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·))
    code := addFn adx false
    contract := addCachedContract X86_64.abi false
    verified := addProjAdx_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addAffineExtApi with
    target := X86_64.target
    doc := addAffineExtApi.doc (notes := (affNotes baseMul).map ("Uses baseline integer instructions, and SSE2 moves. " ++ ·))
    code := addAffineFn baseline
    contract := addAffineContract X86_64.abi true
    verified := addAffine_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addAffineExtApi with
    target := X86_64.target
    name := addAffineExtApi.name ++ "_adx"
    doc := addAffineExtApi.doc (notes := (affNotes adxMul).map ("Uses BMI2 and ADX, and SSE2 moves. " ++ ·))
    code := addAffineFn adx
    contract := addAffineContract X86_64.abi true
    verified := addAffineAdx_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519R64.X86_64
