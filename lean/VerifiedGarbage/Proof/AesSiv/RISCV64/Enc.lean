module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Entry
public import VerifiedGarbage.Proof.AesSiv.RISCV64.S2v
import VerifiedGarbage.Proof.AesSiv.RISCV64.Long
import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
import VerifiedGarbage.Proof.AesSiv.RISCV64.Fn
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Ctr
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Short

/-!
# AES-SIV on RISC-V: `encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves our caller's
registers, computes S2V's first state and S2V of the associated data
(`encS2v_wp`); `encrypt` then finishes S2V with the plaintext into `W`, which
is the synthetic IV `V`, encrypts the plaintext in place by CTR from `V`'s
counter, copies `V` to `siv` and restores our caller's registers
(`encrypt_wp`). Everything but the data and `siv` that the code writes is in
`W`, which the key context, the descriptors and the components miss
(`WF`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64
open VG.Spec.Aes (bytesAt)

/-! ## Writes within `W` -/

/-- A frame within `W`. -/
abbrev WF (c : Cx) (m m' : Mem) : Prop := Frame [⟨c.W, 2576⟩] m m'

theorem WF.of {c : Cx} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨c.W, 2576⟩) : WF c m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem WF.trans {c : Cx} {m₁ m₂ m₃ : Mem} (h₁ : WF c m₁ m₂) (h₂ : WF c m₂ m₃) : WF c m₁ m₃ :=
  Frame.trans h₁ h₂

theorem wR_sub {c : Cx} : ∀ r ∈ wR c, Region.Sub r ⟨c.W, 2576⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem oR_sub {c : Cx} {out : Nat} (h : out + 16 ≤ 2576) : ∀ r ∈ oR c out, Region.Sub r ⟨c.W, 2576⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Lay.wSub h
  · exact wR_sub r hr

theorem WF.ctxMac {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') :
    Spec.Siv.ctxMac m' c.C c.R = Spec.Siv.ctxMac m c.C c.R :=
  ctxMac_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.c_w) L.rb

theorem WF.ctxCiph {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') :
    Spec.Siv.ctxCiph m' c.C c.R = Spec.Siv.ctxCiph m c.C c.R :=
  ctxCiph_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.c_w) L.rb

theorem WF.data {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') : bytesAt m' c.D c.n = bytesAt m c.D c.n :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.d_w) (by have := L.n_lt; omega)

theorem WF.descW {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {i j : Nat} (hi : i < c.N) (hj : j < 2) :
    descW m' c.A i j = descW m c.A i j := by
  have aw := L.aw
  exact h.readW (r := ⟨c.A + BitVec.ofNat 64 (16 * i + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.a_w.sub_left (Offset.sub_base _ (by omega))) (by decide)

theorem WF.ads {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {s : State} (hA : Ads c m s) : Ads c m' s :=
  fun i hi => by rw [h.descW L hi (by decide), h.descW L hi (by decide)]; exact hA i hi

/-- The `i`-th region the descriptors list. -/
theorem listed_eq (m : Mem) (A : Addr) (i : Nat) :
    (⟨(m.readW (A + BitVec.ofNat 64 (i * (2 * (64 / 8)))) 64).setWidth 64,
      (m.readW (A + BitVec.ofNat 64 (i * (2 * (64 / 8))) + BitVec.ofNat 64 (64 / 8)) 64).toNat * Elem.size .u8⟩ :
        Region) = ⟨descW m A i 0, (descW m A i 1).toNat⟩ := by
  simp only [descW, BitVec.setWidth_eq, Elem.size, Nat.mul_one]
  rw [show i * (2 * (64 / 8)) = 16 * i + 8 * 0 by omega, show (64 / 8 : Nat) = 8 from rfl, Offset.add_add,
    show 16 * i + 8 * 0 + 8 = 16 * i + 8 * 1 by omega]

theorem WF.components {c : Cx} (L : Lay c) {m m' : Mem} (h : WF c m m') {s : State} (hA : Ads c m s) :
    Spec.Siv.components 64 m' c.A c.N = Spec.Siv.components 64 m c.A c.N := by
  refine Proof.AesSiv.components_congr fun r hr a ha => (h a fun r' hr' hc => ?_).symm
  simp only [List.mem_singleton] at hr'; subst hr'
  rcases List.mem_cons.mp hr with rfl | hr
  · refine L.a_w a ?_ hc
    simp only [Sig.descRegion, Region.Contains] at ha ⊢
    omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hb := (hA i (List.mem_range.mp hi)).w
    rw [listed_eq] at ha
    exact hb a ha hc

/-! ## S2V of the associated data -/

/-- What S2V of the associated data leaves, from the state `σ` at the entry
and the state `s₁` after it. -/
structure S2vDone (c : Cx) (σ s₁ s : State) : Prop where
  en : Entered c σ s₁
  inv : AInv c s₁ c.N s

theorem encS2v_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s₁ s', S2vDone c s s₁ s' → s'.gpr .s6 = c.D → s'.gpr .s7 = BitVec.ofNat 64 c.n → WP isa rest s' Q) :
    WP isa (.seq encS2v rest) s Q := by
  have L := Ar.lay
  unfold encS2v
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.mono (entry_wp Ar) fun s₁ En => ?_)))
  have E₁ := En.env
  refine WP.mono (WP.seq_iff.mp (start_wp L E₁)) fun s₂' h => WP.seq (WP.mono h fun s₂ ⟨K₂, f₂, d₂⟩ => ?_)
  have wf₁ : WF c s.mem s₁.mem := WF.of En.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  have I₀ : AInv c s₁ 0 s₂ :=
    { env := E₁.of_pk K₂.pk
      pk := K₂.pk
      ads := (wf₁.ads L hA).of_eq (by rw [K₂.pk.rd, En.rd]) (by rw [K₂.pk.wr, En.wr])
      s4 := by rw [K₂.s4, En.s4, Nat.mul_zero, BitVec.add_zero]
      s5 := by rw [K₂.s5, En.s5, Nat.sub_zero]
      frame := f₂
      acc := by rw [d₂, List.take_zero]; rfl }
  refine WP.seq (WP.mono (s2vAds_wp L I₀) fun s₃ I₃ => ?_)
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
  have pk₅ : PK s₃ s₅ := (PK.ofUpd u₄).trans (PK.ofUpd u₅)
  refine k s₁ s₅ ⟨En, ⟨I₃.env.of_pk pk₅, I₃.pk.trans pk₅, I₃.ads.of_eq pk₅.rd pk₅.wr,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), I₃.s4],
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), I₃.s5],
      by rw [u₅.mem, u₄.mem]; exact I₃.frame, by rw [u₅.mem, u₄.mem]; exact I₃.acc⟩⟩
    (by rw [u₅.other _ (by decide), u₄.gpr, I₃.env.s9])
    (by rw [u₅.gpr, u₄.other _ (by decide), I₃.env.s10])

/-- The facts of `S2vDone` about the entry's memory. -/
theorem S2vDone.facts {c : Cx} (L : Lay c) {σ s₁ s : State} (h : S2vDone c σ s₁ s) (hA : Ads c σ.mem σ) :
    WF c σ.mem s.mem ∧ bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16 =
      Spec.Siv.s2vAcc (Spec.Siv.ctxMac σ.mem c.C c.R) (Spec.Siv.components 64 σ.mem c.A c.N) := by
  have wf₁ : WF c σ.mem s₁.mem := WF.of h.en.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  refine ⟨wf₁.trans (WF.of h.inv.frame wR_sub), ?_⟩
  rw [h.inv.acc, List.take_of_length_le (by rw [length_components]), wf₁.ctxMac L, wf₁.components L hA]

/-! ## `encrypt` -/

theorem mutR_wR {c : Cx} : ∀ r ∈ wR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

theorem mutR_oR {c : Cx} {out : Nat} (h : out + 16 ≤ 128) : ∀ r ∈ oR c out, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact sub_lo h
  · exact mutR_wR r hr

theorem mutR_ctrR {c : Cx} : ∀ r ∈ ctrR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_data
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)

theorem ctrR_W0 {c : Cx} (L : Lay c) :
    ∀ r ∈ ctrR c, (⟨c.W + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.d_w' (by decide)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- `vg_aes_siv_encrypt`: `encryptWith`'s synthetic IV at `siv` and ciphertext
at `data`. -/
theorem encrypt_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) (hV : Covers [⟨c.V, 16⟩] s.wr) :
    WP isa encrypt s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.ctxCiph s.mem c.C c.R)
          (Spec.Siv.components 64 s.mem c.A c.N) (bytesAt s.mem c.D c.n) =
        (bytesAt s'.mem c.V 16, bytesAt s'.mem c.D c.n) := by
  have L := Ar.lay
  unfold encrypt
  refine encS2v_wp Ar hA fun s₁ s₄ S h6 h7 => ?_
  obtain ⟨wf₄, acc₄⟩ := S.facts L hA
  have E₄ := S.inv.env
  refine WP.seq (WP.mono (finish_wp L E₄ (L.bufD E₄.perm) h6 h7 (out := 0) (.inl rfl))
    fun s₅ ⟨pk₅, f₅, v₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have wf₅ : WF c s.mem s₅.mem := wf₄.trans (WF.of f₅ (oR_sub (by decide)))
  refine WP.seq (WP.mono (ctr_wp L E₅ (src := 0) (by decide) (by decide)) fun s₆ ⟨pk₆, f₆, d₆⟩ => ?_)
  have E₆ := E₅.of_pk pk₆
  have pk₁₆ : PK s₁ s₆ := S.inv.pk.trans (pk₅.trans pk₆)
  refine WP.block_append_iff.mpr (WP.mono (sivOut_wp L E₆ (by rw [pk₁₆.wr, S.en.wr]; exact hV))
    fun s₇ ⟨pk₇, f₇, v₇⟩ => ?_)
  have E₇ := E₆.of_pk pk₇
  have pk₁₇ : PK s₁ s₇ := pk₁₆.trans pk₇
  -- Our caller's registers, in their slots.
  have fm : Frame (mutR c) s₁.mem s₆.mem :=
    ((S.inv.frame.sub mutR_wR).trans (f₅.sub (mutR_oR (by decide)))).trans (f₆.sub mutR_ctrR)
  have sv₇ : Spill.Saved c.W s.gpr savedL s₇.mem :=
    (saved_mut L fm S.en.saved).frame_in savedL_bound f₇ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.v_w' (by decide)).symm
  refine WP.mono (exit_wp L E₇ sv₇ (by rw [pk₁₇.sp, S.en.sp])) fun s₈ ⟨ab, m₈, _⟩ => ⟨ab, ?_⟩
  -- The synthetic IV and the ciphertext.
  have v₆ : bytesAt s₆.mem c.W 16 = bytesAt s₅.mem c.W 16 := by
    have := Proof.Cmac.bytesAt_frame f₆ (ctrR_W0 L) (by decide)
    rwa [BitVec.add_zero] at this
  rw [BitVec.add_zero] at v₅ d₆
  rw [Spec.Siv.encryptWith_eq, Spec.Siv.sealWith]
  have hv : bytesAt s₈.mem c.V 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.components 64 s.mem c.A c.N))
      (bytesAt s.mem c.D c.n) := by
    rw [m₈, v₇, v₆, v₅, wf₄.ctxMac L, wf₄.data L, acc₄]
  have hd : bytesAt s₈.mem c.D c.n = bytesAt s₆.mem c.D c.n := by
    rw [m₈]
    exact Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.v_d.symm) (by have := L.n_lt; omega)
  rw [hv, hd, d₆, wf₅.ctxCiph L, wf₅.data L, v₅, wf₄.ctxMac L, wf₄.data L, acc₄]

end VG.Proof.AesSiv.RISCV64
