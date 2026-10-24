module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSLoad
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: numbers out of the key working space

`storeS_vp`: the claim at byte `o` of `scratch` := `[j]`'s low `n` bytes,
big-endian (`storeBytes_ok`), run on the whole state, whose `scratch` holds
the key working space (`SS.wsFull`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws storeBytes_ok bytes_of_store)
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s : State}

/-- The key working space, within `scratch`, on the whole state. -/
theorem SS.wsFull (h : SS G STK σ c s) (hr : KR G s) : Ws s G.KB (kz G.pLen) G.w nArrs := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit
  have e := h.kbNat
  have l := h.lens
  have inS : G.rScr ∈ s.wr := by rw [h.gi.wr, h.gi.pre.wr, h.gi.hG]; simp
  refine ⟨⟨⟨G.scr, kB G.pLen, G.scrLen * 8, inS, rfl, by omega, by omega⟩, by omega⟩,
    ?_, ?_, ?_, hr.r29, hr.r30, hr.r31⟩ <;>
    simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr, nArrs, kz, GP.w] <;> rcases l with e | e | e <;> rw [e] <;> decide

end

/-- Bytes outside `[O, O + L)` kept, as a frame. -/
theorem frame_of_outside {O : Addr} {L : Nat} {m m' : Mem} (h : VG.Proof.Bignum.Outside O 0 L m m') :
    Frame [⟨O, L⟩] m m' := fun x hx => h x (.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  show 0 + L ≤ (x - O).toNat
  omega))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The taint analysis of a store, its destination, length and mask public. -/
abbrev CertS (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.PPC64LE.taint
  (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes j) hc).isSome = true

/-- The claim at byte `o` of `scratch` := `[j]`'s low `n` bytes, big-endian. -/
theorem storeS_vp {j o n : Nat} (cert : CertS j) (hj : j ∈ c.live) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w)
    (ho15 : o < 2 ^ 15) (hn15 : n < 2 ^ 15) (hoc : ∀ σ s, St G c X σ s → ClOk G (o, List.replicate n 0))
    {cl' : Claims} (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart o n x) :
    VP (KSt G c X) (storeS j o n)
      (KSt G { c with cl := (o, Spec.Rsa.i2osp (c.A j % 2 ^ (8 * n)) n) :: cl' } X) := by
  refine VP.seq (G := fun σ s => KSt G c X σ s ∧ s.gpr .r5 = G.sa o ∧ s.gpr .r8 = BitVec.ofNat 64 n ∧
      s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if true then 1 else 0))
    (VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.gi.r28, by rw [hs.1.1.gi.sp, ← hs.1.1.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
        (.block [scr .r5 o, .li .r8 n, .li .r9 0, .subi .r9 .r9 1]), rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_) ?_
  · refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) ho15) fun s₁ u₁ sp₁ _ => ?_
    refine WP.wr (exec_li hn15) fun s₂ u₂ sp₂ _ => ?_
    refine WP.wr (exec_li (by decide)) fun s₃ u₃ sp₃ _ => ?_
    refine WP.wr (exec_subi (by decide) (by decide)) fun t u sp _ => WP.block_nil fun _ => ?_
    have K : Keep [.r5, .r8, .r9] s t := ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u.other _ hr.2.2, u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1],
      by rw [u.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    refine ⟨⟨⟨h.of_keep K (by rw [u.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [sp, sp₃, sp₂, sp₁]), x⟩,
      kr.of_keep K⟩, ?_, ?_, ?_⟩
    · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.gi.r28]
    · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    · rw [u.gpr, u₃.gpr]; rfl
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.r28, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31, .r5, .r8, .r9] cert (fun σ₁ σ₂ s₁ s₂ ⟨⟨_, a⟩, a5, a8, a9⟩ ⟨⟨_, b⟩, b5, b8, b9⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]
      · rw [a5, b5]
      · rw [a8, b8]
      · rw [a9, b9]) fun σ s ⟨⟨⟨h, x⟩, kr⟩, p5, p8, p9⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hw := h.wsFull kr
  have l := h.lens
  have hjN := h.liveOk j hj
  have ok := hoc σ s ⟨h, x⟩
  simp only [ClOk, List.length_replicate] at ok
  have va := h.arrs.get hj
  have hsep : Region.Disjoint ⟨G.sa o, n⟩ G.rK := (gi.kdisj ok.2.1 ok.2.2).symm
  have hc : ∀ i < n, (⟨G.sa o, n⟩ : Region).Contains (G.sa o + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (storeBytes_ok hw hjN (by decide) p5 p8 p9 hn0 hnw
    (fun i hi => by
      show InRegions s.wr (G.sa o + BitVec.ofNat 64 i) 1
      rw [GP.sa_add]; exact gi.inScr (by omega) (by omega))
    (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' hsep (hc i hi)) (Nat.not_le.mpr hx))
    (by rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)) fun t ⟨_, bt, ot, kt⟩ => ⟨⟨?_, x⟩, kr.of_keep ⟨kt.gpr, kt.rd, kt.wr⟩⟩
  have bs : Spec.Rsa.bytesAt t.mem (G.sa o) n = Spec.Rsa.i2osp (c.A j % 2 ^ (8 * n)) n := by
    rw [bytes_of_store hnw fun i hi => by rw [bt i hi]; rfl, Nat.pow_mul, va]
  refine h.of_scrs ⟨kt.gpr, kt.rd, kt.wr⟩ kt.sp (os := [(o, n)]) (fun p hp => ?_)
    ((frame_of_outside ot).mono (by simp)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length]; exact bs, by simp only [ClOk, VG.Proof.Rsa.i2osp_length]; omega⟩
  · exact .inl ⟨(hcl y hy).1, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hcl y hy).2⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
