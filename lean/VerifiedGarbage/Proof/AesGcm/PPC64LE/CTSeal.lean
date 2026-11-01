module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealEntry
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFusedCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFusedCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry loads `W` from the
stack argument at `sp + 104`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`oneHead_ct`). The pieces follow (`CTOne.lean`), with the
tag's address `T` in `r20`, which the environment pins, and, between them,
the additional data absorbed, for `oneTag 0`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The entry of `seal`, from its precondition. -/
theorem sealEntry_wp {s₀ : State} (h : sealPre s₀) :
    WP isa (.block (oneEntry 104)) s₀ fun s₁ =>
      OneI (s₀.gpr .r3) (stackArg s₀ 1) s₀.sp (s₀.gpr .r4).toNat (s₀.gpr .r5) (s₀.gpr .r6).toNat (s₀.gpr .r7)
        (s₀.gpr .r8) (s₀.gpr .r9) (s₀.gpr .r10) s₁ ∧
      s₁.gpr .r24 = s₀.gpr .r5 ∧ s₁.gpr .r25 = BitVec.ofNat 64 (s₀.gpr .r6).toNat ∧
      s₁.gpr .r20 = stackArg s₀ 0 ∧ Covers [⟨stackArg s₀ 0, 16⟩] s₁.wr := by
  exact WP.mono (SealEntry.entry_wp (SealAccess.of_pre h)) fun _ h1 =>
    SealEntry.entry_ready (SealAccess.of_pre h) h1


section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64}

/-- `OneI`, with the tag's address `T` in `r20`, which the state may write. -/
def OneT (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln T : BitVec 64) (s : State) : Prop :=
  OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .r20 = T ∧ Covers [⟨T, 16⟩] s.wr

theorem OneT.keep {s s' : State} (h : OneT c W sp R Np n Ad A D Ln T s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    OneT c W sp R Np n Ad A D Ln T s' :=
  ⟨h.1.keep hV he hrd hwr, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1), by rw [hwr]; exact h.2.2⟩

/-- Between `oneAad` and `oneTag`: the additional data `a` absorbed and padded. -/
def OneAbs (c W : Addr) (A : BitVec 64) (s : State) : Prop :=
  ∃ H : Block, ∃ a : List Byte, blockAt s.mem (c + BitVec.ofNat 64 240) = H ∧ A.toNat = a.length ∧
    Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length))

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩)
include L hR hTW

/-- `seal` after its entry. -/
theorem sealWithBody_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {textBody : Prog isa}
    (bodyCorrect : SealFused.BodyCorrect textBody)
    (bodyCT : CT (OneI c W sp R Np n Ad A D Ln) textBody) : CT (fun s => OneT c W sp R Np n Ad A D Ln T s ∧ s.gpr .r24 = Np ∧
    s.gpr .r25 = BitVec.ofNat 64 n)
    (.seq oneAad (.seq textBody (.seq (.block tagOut) (.block restore)))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, g, i]; exact hA))) fun s' ⟨oa, rd, wr, _⟩ => ⟨hT.keep (fun r hr => (he.fr r hr).symm) oa.env rd wr,
        blockAt s.mem (V .r29 + BitVec.ofNat 64 240), bytesAt s.mem (V .r21) (V .r22).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .r31 = W ∧ V .r20 = T ∧ Env V sp s ∧
    Covers [⟨T,16⟩] s.wr) (bodyCT.mono fun _ hs => hs.1.1)
    (fun s ⟨hT,H,x,hH,hl,hab⟩ => ?_) ?_
  · obtain ⟨V,a,b,d,e,f,g,i,j,k,he,hN,hA,hD⟩ := hT.1
    have hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by
      rw [a,b,d,j,k]; exact hD
    have hab' : Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
        (x++zeros (padLen x.length)) := by
      rw [ctxH_eq,a,hH,b]; exact hab
    exact WP.mono (WP.with_rdwr (bodyCorrect (L.v a b d) he hd e hR (by rw [i]; exact hl) hab'))
      fun s' ⟨bo,_,wr,_⟩ => ⟨V,d,(he.fr _ (by decide)).symm.trans hT.2.1,bo.env,
        by rw [wr]; exact hT.2.2⟩
  exact SealEntry.return_ct hTW

end

theorem sealWith_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {textBody : Prog isa}
    (bodyCorrect : SealFused.BodyCorrect textBody)
    (bodyCT : ∀ {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln : BitVec 64},
      Lay c (W+BitVec.ofNat 64 16) W → (R=10 ∨ R=12 ∨ R=14) →
      CT (OneI c W sp R Np n Ad A D Ln) textBody) :
    ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub (sealWith textBody) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have h₁' : sealPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, fW, _, hR⟩ := h₁'
  let I₀ : State → Prop := fun s => sealPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm, (qa 1 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .r3) (stackArg σ₁ 1) σ₁.sp (σ₁.gpr .r4).toNat (σ₁.gpr .r5)
    (σ₁.gpr .r6).toNat (σ₁.gpr .r7) (σ₁.gpr .r8) (σ₁.gpr .r9) (σ₁.gpr .r10) (stackArg σ₁ 0) s ∧
    s.gpr .r24 = σ₁.gpr .r5 ∧ s.gpr .r25 = BitVec.ofNat 64 (σ₁.gpr .r6).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1⟩ => ?_)
    (sealWithBody_ct (oneLay fc fW dcW) hR (dtW.sub_right (Region.sub_prefix (by decide)))
      bodyCorrect (bodyCT (oneLay fc fW dcW) hR))
  · exact SealEntry.entry_ct (I := I₀) (v := σ₁.gpr) (sp := σ₁.sp) (W := stackArg σ₁ 1)
      (fun s hs => SealAccess.of_pre hs.1)
      (fun s ⟨_,e3,e4,e5,e6,e7,e8,e9,e10,esp,_,ea1⟩ => ⟨esp,by
        intro r hr
        simp only [SealEntry.entryRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption,ea1⟩)

  · have := sealEntry_wp hs
    rw [ea0, ea1, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT⟩ => ⟨⟨hO, h20, hT⟩, h24, h25⟩

theorem seal_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub «seal» :=
  sealWith_ct (fun L he hd hR hv ha hab => SealFused.smallBody_ok L he hd hR hv ha hab)
    (fun L hv => SealFusedCT.smallBody_ct L hv)

theorem sealFused_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub Impl.AesGcm.PPC64LE.SealFused.seal :=
  sealWith_ct (fun L he hd hR hv ha hab => SealFused.body_ok L he hd hR hv ha hab)
    (fun L hv => SealFusedCT.body_ct L hv)

end VG.Proof.AesGcm.PPC64LE
