import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- The four divstep matrix coefficients are register inputs, beyond the scratch-word names. -/
def matrixEnv (size : Nat) : Env Nat :=
  {initialEnv with reg:=fun r =>
    if r=.x4 then some (size/8+1) else
    if r=.x5 then some (size/8+2) else
    if r=.x6 then some (size/8+3) else
    if r=.x7 then some (size/8+4) else none}

def matrixNodes (size : Nat) : Array Node :=
  initialNodes size ++ #[.input size,.input (size+8),.input (size+16),.input (size+24)]

def matrixInput (size : Nat) (s : State) (base : Addr) (off : Nat) : BitVec 64 :=
  if off<size then word s.mem base off else
  if off=size then s.gpr .x4 else
  if off=size+8 then s.gpr .x5 else
  if off=size+16 then s.gpr .x6 else s.gpr .x7

/-- The initial relation imposes no restrictions on the four matrix coefficients. -/
theorem matrix_initial_rel {nodes : Certificate} {size : Nat} (hi : Inputs nodes size)
    (h4 : nodes.nodes.lookup (size/8+1)=some (.input size))
    (h5 : nodes.nodes.lookup (size/8+2)=some (.input (size+8)))
    (h6 : nodes.nodes.lookup (size/8+3)=some (.input (size+16)))
    (h7 : nodes.nodes.lookup (size/8+4)=some (.input (size+24)))
    (s : State) (base : Addr) :
    Rel (nodeVal nodes (matrixInput size s base)) base size (matrixEnv size) s := by
  refine ⟨?_,?_,?_⟩
  · intro r a h
    simp only [matrixEnv] at h
    split at h
    · rename_i hr
      subst r
      cases h
      simp [nodeVal,h4,matrixInput]
    · split at h
      · rename_i hr
        subst r
        cases h
        simp only [nodeVal,h5,matrixInput]
        split <;> (try omega)
        split <;> (try omega)
        rfl
      · split at h
        · rename_i hr
          subst r
          cases h
          simp only [nodeVal,h6,matrixInput]
          split <;> (try omega)
          split <;> (try omega)
          split <;> (try omega)
          rfl
        · split at h
          · rename_i hr
            subst r
            cases h
            simp only [nodeVal,h7,matrixInput]
            split <;> (try omega)
            split <;> (try omega)
            split <;> (try omega)
            split <;> (try omega)
            rfl
          · cases h
  · intro off ha hb
    change (nodeVal nodes (matrixInput size s base) (off/8+1)).1=_
    rw [nodeVal,hi off ha hb]
    simp only [matrixInput,show off<size by omega,↓reduceIte]
  · intro a h; cases h

end VG.Proof.Weierstrass.AArch64.Forward
