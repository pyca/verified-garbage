module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfAddress
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacFinalizePre

/-! # Prepare a PRF HMAC finalization with a public indexed output -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def prfFinalizePrefix (len : Nat) : Nat → CallArg
  | 0 => .scratch sSt | 1 => .scratch sOuter | 2 => .value (64 + len) | _ => .value 0

theorem argsFrame_counter {g : Geometry} {m m' : Mem}
    (F : Frame [⟨byteAddr g.stack, 80⟩] m m') :
    m'.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 =
      m.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 := by
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint_base _ (by decide : 80 ≤ oI) (by decide)

theorem prfFinArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s)
    (len dst i : Nat) (counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i) :
    WP isa (.block (prfFinArgs len dst)) s fun t => Context g bs t ∧
      Arguments g (macFinalizeValues g (dst + 32 * i) (64 + len)) 6 t ∧
      Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have code : prfFinArgs len dst =
      ((List.range 4).flatMap fun j => (prfFinalizePrefix len j).code j) ++
      prfDstArgs dst ++ scratchArg sHash 5 := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (plan_ok h (prfFinalizePrefix len) 4 (by decide) ?_) ?_
  · intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> trivial
  · rintro a ⟨ha, argsA, Fa, Ka⟩
    have args4 : Arguments g (macFinalizeValues g (dst + 32 * i) (64 + len)) 4 a := by
      intro j hj
      rw [argsA j hj]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
      · exact BitVec.add_zero _
      all_goals rfl
    refine WP.mono (prfDstArgs_ok ha dst i ((argsFrame_counter Fa).trans counter)) ?_
    rintro b ⟨hb, Mb, Fb, Kb⟩
    have args5 : Arguments g (macFinalizeValues g (dst + 32 * i) (64 + len)) 5 b :=
      args4.append (by decide : 4 < 20) Mb Fb
    refine WP.mono (prepareArgument_ok args5 (by decide : 5 < 20) (scratchArg_ok hb sHash (by decide : 5 < 20))) ?_
    rintro t ⟨ht, argsT, Ft, Kt⟩
    exact ⟨ht, argsT, Fa.trans ((slotFrame_outgoing (by decide : 4 < 20) Fb).trans Ft),
      (Ka.mono (by decide)).trans (Kb.trans (Kt.mono (by decide)))⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
