module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Data
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Omega

/-! # The FFDH controllers' frames (RISC-V)

Aligned doublewords at offsets, and a frame saving a register around a body
that may have frames of any kind (`WP.frameRegAny`), for the controllers of
`Proof/Ffdh/RISCV64/Cached/SearchProof/` and
`Proof/Ffdh/RISCV64/Generation/Search/`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.KeyGeneration

open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64

/-- A doubleword at an offset that is a multiple of 8 from an aligned base. -/
theorem al8 {B : Addr} (hB : B.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) :
    (B + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega


/-- A frame saving `r` around `main`, which may have frames of any kind:
`main` runs from `s₀` with the stack pointer moved down by 16 and `r` stored
8 bytes above it, in the permissions of `s₀`, and the pop restores `r` and
the stack pointer. -/
theorem WP.frameRegAny {r : Reg} {main : Prog isa} {s₀ : State} {Q : State → Prop}
    (hsp : 16 ≤ s₀.sp.toNat) (hd : ∀ R ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 16, 16⟩ R)
    (hmain : WP isa main (framed r s₀) fun s₂ => Q { s₂.write r (s₀.gpr r) with sp := s₀.sp })
    (hn : sdepth main + 16 < 2 ^ 64) :
    WP isa (.frame (.push r) main (.pop r)) s₀ Q := by
  refine WP.frame hsp (WP.narrowAny (rd := s₀.rd) (wr := s₀.wr) hmain ?_ ?_ ?_ (by omega))
  · intro a n hi
    exact InRegions_append_cons.mpr (.inr hi)
  · intro a n hi
    exact InRegions_append_cons (xs := []).mpr (.inr hi)
  · intro s' hrd hwr hsp' hf hq
    have hread : s'.mem.read (s'.sp + 8) 8 = s₀.gpr r := by
      rw [hsp', show (pushed r s₀).sp = s₀.sp - 16 from rfl,
        hf.read (r := ⟨s₀.sp - 16, 16⟩) (frame_contains s₀.sp) (fun R hR => ?_) (by decide)]
      · exact read_write_self _ _ _
      · rcases List.mem_append.mp hR with hR | hR
        · exact hd R hR
        · simp only [List.mem_singleton] at hR; subst hR
          exact frame_not_below s₀.sp hn
    have e : popped r s' = { (s'.withRegions s₀.rd s₀.wr).write r (s₀.gpr r) with sp := s₀.sp } := by
      simp only [popped, hread]
      simp only [hsp', hwr, pushed, List.tail_cons, BitVec.sub_add_cancel]
      cases s'
      simp only [pushed] at hrd
      subst hrd
      rfl
    rw [e]; exact hq


end VG.Proof.Ffdh.RISCV64.KeyGeneration
