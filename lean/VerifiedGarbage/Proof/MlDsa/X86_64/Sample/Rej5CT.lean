module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlDsa.Sample.Hash
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Vec
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt
import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Vec
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.MlKem.KPke

/-! ### `MlDsa.X86_64.Sample.Rej5Batch`, which only this module used -/

section

/-! ### `MlDsa.X86_64.Sample.Rej5Parse`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (setup parse)
open VG.Proof.MlKem.X86_64.S4 (wp_vtbl)
open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half)
open VG.Proof.MlKem.X86_64 (Keep ea_at wp_countdown add_ofNat_zero pR WP.keep ofNat64_pred)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold rnStep rnFold_snoc rnFold_length_le Stored stored_nil stored_frame G_eq G_length)
open VG.Proof.MlDsa.X86_64.Sample (rnBody_ok CoeffsWr)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlKem (xofByte xof_squeezeFrom_getElem)

structure HAt (σ s₀ : State) (K h off count t : Nat) (s : State) : Prop where
  env : EnvK σ s
  rsi : s.gpr .rsi = at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * (off + t))
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ K (168 * h + off + t)).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (count - t)
  rbp : s.gpr .rbp = Proof.MlKem.poly4 (aP σ) K
  out : ∀ p < 3 * (off + count), s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (504 * h + p)
  stored : Stored s.mem (Proof.MlKem.poly4 (aP σ) K) (Lt σ K (168 * h + off + t))
  fr : Frame [pR (Proof.MlKem.poly4 (aP σ) K)] s₀.mem s.mem
  kp : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp] s₀ s

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem hat_byte {s₀ : State} {K h off count t : Nat} (hh : h < 2) (hspan : off + count ≤ 168) {s : State} (hI : HAt σ s₀ K h off count t s) {j : Nat}
    (hj : 3 * (off + t) + j < 3 * (off + count)) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 j) = (Xb σ K).getD (3 * (168 * h + off + t) + j) 0 := by
  obtain e := hI.out (3 * (off + t) + j) hj
  rw [at'] at e
  rw [hI.rsi, at', Offset.add_add, Offset.add_add, e, Xb_getD σ K (by omega_using [hh, hspan, hj])]
  congr 1; omega_using []

theorem hat_regions {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) {s : State} (hI : HAt σ s₀ K h off count t s) {j : Nat}
    (hj : 3 * (off + t) + j < 3 * (off + count)) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [hI.rsi, at', Offset.add_add, Offset.add_add]
  exact in_scr' hp hI.env.rd hI.env.wr (by simp only [oBuf]; omega_using [hK, hspan, hj])

/-- An iteration. -/
theorem hat_step {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (ht : t < count) {s : State}
    (hI : HAt σ s₀ K h off count t s) :
    WP isa rnBody s fun s' => HAt σ s₀ K h off count (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (count - t) - 1 == 0) := by
  refine WP.mono (rnBody_ok s (aP := Proof.MlKem.poly4 (aP σ) K) hI.rbp hI.rdi (Lt_length_le σ K _) (coeffsWr hp hK hI.env)
    hI.stored (by simpa using hat_regions hp hK hspan hI (j := 0) (by omega_using [ht])) (hat_regions hp hK hspan hI (by omega_using [ht]))
    (hat_regions hp hK hspan hI (by omega_using [ht]))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  obtain e0 := hat_byte hh hspan hI (j := 0) (by omega_using [ht])
  rw [add_ofNat_zero, Nat.add_zero] at e0
  obtain ht3 : Lt σ K (168 * h + off + (t + 1)) = rnStep (Lt σ K (168 * h + off + t)) ((Xb σ K).getD (3 * (168 * h + off + t)) 0)
      ((Xb σ K).getD (3 * (168 * h + off + t) + 1) 0) ((Xb σ K).getD (3 * (168 * h + off + t) + 2) 0) := by
    simp only [Lt]
    rw [show 3 * (168 * h + off + (t + 1)) = 3 * (168 * h + off + t) + 3 by omega_using [],
      VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [Xb, G_length]; omega_using [hh, hspan, ht]),
      rnFold_snoc _ (by rw [List.length_take, Xb, G_length]; omega_using [])]
  rw [e0, hat_byte hh hspan hI (j := 1) (by omega_using [ht]), hat_byte hh hspan hI (j := 2) (by omega_using [ht]), ← ht3] at hdi hst
  have hk' : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := hk
  refine ⟨⟨env_poly hp hK hI.env hf hk'.2.1 hk'.2.2 fun r hr => hk'.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, hI.rsi, Offset.add_add, show 3 * (off + t) + 3 = 3 * (off + (t + 1)) by omega_using []], hdi,
    by rw [hcx, hI.rcx, ofNat64_pred (by omega_using [ht]) (by omega_using [hspan])]; rfl,
    by rw [hk'.gpr (by decide), hI.rbp],
    fun p hp' => by
      rw [frame_byte hf (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega_using [hK, hspan, hp']))
        (Region.contains_self _ _)]
      exact hI.out p hp',
    hst, hI.fr.trans hf, (hI.kp.trans hk').mono (by simp)⟩, by rw [hz, hI.rcx]⟩

/-- A segment of the buffer, from iteration zero. -/
theorem hloop_ok {s₀ : State} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (hpos : 0 < count) {s : State} (hI : HAt σ s₀ K h off count 0 s) :
    WP isa (.loop rnBody .ne) s (HAt σ s₀ K h off count count) := by
  refine wp_countdown (N := count) (by omega_using [hspan]) (by omega_using [hpos]) (fun t u => HAt σ s₀ K h off count t u)
    (fun t ht u hu _ => WP.mono (hat_step hp hK hh hspan ht hu) fun u' ⟨hu', hz⟩ => ⟨hu', ?_, by rw [hz, hu.rcx]⟩)
    (fun _ h => h) hI hI.rcx
  rw [hu'.rcx, hu.rcx, ofNat64_pred (by omega_using [ht]) (by omega_using [hspan])]; rfl


/-- Before a bounded segment of one seed's buffer. -/
structure HPre (σ : State) (K h off count : Nat) (s : State) : Prop where
  env : EnvK σ s
  out : ∀ p < 3 * (off + count), s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (504 * h + p)
  j : s.mem.readW (at' σ (oJ + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K (168 * h + off)).length
  stored : Stored s.mem (Proof.MlKem.poly4 (aP σ) K) (Lt σ K (168 * h + off))

/-! ## Eight candidates at a time -/

/-- After `t` candidates of a segment of `count` candidates at `off`, from `s₀`. -/
structure GB (σ s₀ : State) (K h off count t : Nat) (s : State) : Prop where
  env : EnvK σ s
  rsi : s.gpr .rsi = at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * (off + t))
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ K (168 * h + off + t)).length
  rbp : s.gpr .rbp = Proof.MlKem.poly4 (aP σ) K
  out : ∀ p < 3 * (off + count), s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (504 * h + p)
  stored : Stored s.mem (Proof.MlKem.poly4 (aP σ) K) (Lt σ K (168 * h + off + t))
  fr : Frame [pR (Proof.MlKem.poly4 (aP σ) K)] s₀.mem s.mem
  kp : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp, .r10, .r11] s₀ s
  /-- While the vector code may run: its constants, and the static's address. -/
  vec : (Lt σ K (168 * h + off + t)).length ≤ 248 → Vec.VC s ∧ s.gpr .r11 = s.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName

omit hp in
/-- One more iteration of the loop of `RejNTTPoly`, on the next three bytes. -/
theorem Lt_succ (σ : State) (K : Nat) {m : Nat} (hm : 3 * m + 3 ≤ 1008) :
    Lt σ K (m + 1) = rnStep (Lt σ K m) ((Xb σ K).getD (3 * m) 0) ((Xb σ K).getD (3 * m + 1) 0)
      ((Xb σ K).getD (3 * m + 2) 0) := by
  simp only [Lt]
  rw [show 3 * (m + 1) = 3 * m + 3 by omega_using [],
    VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [Xb, G_length]; omega_using [hm]),
    rnFold_snoc _ (by rw [List.length_take, Xb, G_length]; omega_using [])]

omit hp in
/-- `k` more iterations, as `stepsG` on the bytes from `3 m`. -/
theorem Lt_steps (σ : State) (K m : Nat) : ∀ k, 3 * (m + k) ≤ 1008 →
    Lt σ K (m + k) = Vec.stepsG (Lt σ K m) (fun p => (Xb σ K).getD (3 * m + p) 0) k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [← Nat.add_assoc, Lt_succ σ K (by omega_using [hk]), Lt_steps σ K m k (by omega_using [hk]), Vec.stepsG]
    simp only [show 3 * (m + k) = 3 * m + 3 * k by omega_using [], Nat.add_assoc]

omit hp in
theorem stepsG_length_ge (a : List Zq) (g : Nat → Byte) : ∀ k, a.length ≤ (Vec.stepsG a g k).length
  | 0 => Nat.le_refl _
  | k + 1 => by
    rw [Vec.stepsG]
    refine Nat.le_trans (stepsG_length_ge a g k) ?_
    unfold rnStep; split
    · split <;> simp
    · exact Nat.le_refl _

omit hp in
theorem Lt_mono' (σ : State) (K m k : Nat) (hk : 3 * (m + k) ≤ 1008) : (Lt σ K m).length ≤ (Lt σ K (m + k)).length := by
  rw [Lt_steps σ K m k hk]; exact stepsG_length_ge _ _ k

omit hp in
theorem GB.same {s₀ : State} {K h off count t : Nat} {s s' : State} (hI : GB σ s₀ K h off count t s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (sy : s'.syms = s.syms)
    (hl : ∀ x l, s'.lane x l = s.lane x l) : GB σ s₀ K h off count t s' :=
  ⟨hI.env.keep hm (show Keep [] s s' from ⟨fun r _ => by rw [hg], hrd, hwr⟩) (by decide), by rw [hg, hI.rsi],
    by rw [hg, hI.rdi],
    by rw [hg, hI.rbp], by rw [hm]; exact hI.out, by rw [hm]; exact hI.stored, by rw [hm]; exact hI.fr,
    (hI.kp.trans (show Keep [] s s' from ⟨fun r _ => by rw [hg], hrd, hwr⟩)).mono (by simp),
    fun h' => ⟨(hI.vec h').1.same hl, by rw [hg, sy]; exact (hI.vec h').2⟩⟩

omit hp in
/-- The start of the scalar loop of a group, after `mov ecx, 8`. -/
theorem hat0_of {s₀ : State} {K h off count t : Nat} (ht : t + 8 ≤ count) {s s₁ : State}
    (hI : GB σ s₀ K h off count t s) (hm : s₁.mem = s.mem) (k : Keep [.rcx] s s₁) (hc : s₁.gpr .rcx = BitVec.ofNat 64 8) :
    HAt σ s₁ K h (off + t) 8 0 s₁ :=
  ⟨hI.env.keep hm k (by decide),
    by rw [k.gpr (by decide), hI.rsi, at', Offset.add_add, Offset.add_add, Nat.add_zero],
    by rw [k.gpr (by decide), hI.rdi, Nat.add_zero, Nat.add_assoc], by rw [hc],
    by rw [k.gpr (by decide), hI.rbp], fun p hp' => by rw [hm]; exact hI.out p (by omega_using [ht, hp']),
    by rw [hm, Nat.add_zero, ← Nat.add_assoc]; exact hI.stored, Frame.refl _ _, ⟨fun _ _ => rfl, rfl, rfl⟩⟩

/-- The end of the scalar loop of a group, with more than 248 coefficients. -/
theorem gb_of_hat {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s s₁ s₂ : State}
    (hI : GB σ s₀ K h off count t s) (hm : s₁.mem = s.mem) (k : Keep [.rcx] s s₁)
    (hA' : HAt σ s₁ K h (off + t) 8 8 s₂) (hl : 248 < (Lt σ K (168 * h + off + t)).length) :
    GB σ s₀ K h off count (t + 8) s₂ ∧ s₂.gpr .r10 = s.gpr .r10 := by
  obtain hkp : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp, .r10, .r11] s₀ s₂ :=
    ((hI.kp.trans k).trans hA'.kp).mono (by simp)
  refine ⟨⟨hA'.env, by rw [hA'.rsi]; exact congrArg (fun x => at' σ (oBuf + 504 * K) + BitVec.ofNat 64 x) (by omega_using []),
    by rw [hA'.rdi, show 168 * h + (off + t) + 8 = 168 * h + off + (t + 8) by omega_using []], hA'.rbp,
    fun p hp' => by
      rw [frame_byte hA'.fr (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega_using [hK, hspan, hp']))
        (Region.contains_self _ _), hm]
      exact hI.out p hp',
    by rw [show 168 * h + off + (t + 8) = 168 * h + (off + t) + 8 by omega_using []]; exact hA'.stored,
    hI.fr.trans (by rw [← hm]; exact hA'.fr), hkp,
    fun h' => absurd h' (by
      have := Lt_mono' σ K (168 * h + off + t) 8 (by omega_using [hh, hspan, ht])
      rw [show 168 * h + off + (t + 8) = 168 * h + off + t + 8 by omega_using []]; omega_using [hl, this])⟩,
    by rw [hA'.kp.gpr (by decide), k.gpr (by decide)]⟩

/-- Eight iterations of `vg_mldsa_rej_ntt_poly`'s loop. -/
theorem gsca_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s : State} (hI : GB σ s₀ K h off count t s)
    (hl : 248 < (Lt σ K (168 * h + off + t)).length) :
    WP isa VG.Impl.MlDsa.X86_64.Sample.Rej5.sca8 s fun s' => GB σ s₀ K h off count (t + 8) s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 8)
      (by xrun) rfl) fun s₁ ⟨⟨hm, hc⟩, k⟩ =>
    WP.mono (hloop_ok hp hK hh (by omega_using [hspan, ht]) (by decide) (hat0_of ht hI hm k hc)) fun s₂ hA' =>
      gb_of_hat hp hK hh hspan ht hI hm k hA' hl)

/-- The output of eight iterations is in the polynomial. -/
theorem out_reg {K : Nat} (hK : K < 4) {s : State} (he : EnvK σ s) {n : Nat} (hn : n + 4 ≤ 256) :
    InRegions s.wr (Proof.MlKem.poly4 (aP σ) K + BitVec.ofNat 64 (4 * n)) 16 := by
  rw [he.wr, hp.wr]
  exact ⟨aR σ, by simp, by rw [Proof.MlKem.poly4, Offset.add_add]; exact Offset.contains_base _ (by omega_using [hK, hn]) (by omega_using [hK, hn])⟩

/-- The bytes of the eight candidates at iteration `t`, as `Vec.stepsG` takes them. -/
abbrev gOf (σ : State) (K h off t : Nat) : Nat → Byte := fun p => (Xb σ K).getD (3 * (168 * h + off + t) + p) 0

/-- `s₁` after `vcand` from `s`. -/
abbrev VIF (s s₁ : State) : Prop :=
  (s₁.gpr .rax).toNat = Vec.maskL (s.mem.readW (s.gpr .rsi) 256) 0 + 65536 * Vec.maskL (s.mem.readW (s.gpr .rsi) 256) 1 ∧
    (∀ l < 2, s₁.lane .xmm0 l = Vec.candD (s.mem.readW (s.gpr .rsi) 256) l) ∧ Vec.VC s₁ ∧ s₁.mem = s.mem ∧
    s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.syms = s.syms ∧ ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r

/-- After `vcand`, at iteration `t` with room for eight coefficients. -/
def VI (σ s₀ : State) (K h off count t : Nat) (s₁ : State) : Prop :=
  ∃ s, GB σ s₀ K h off count t s ∧ (Lt σ K (168 * h + off + t)).length ≤ 248 ∧ VIF s s₁

omit hp in
/-- The candidates of the 24 bytes at `rsi` are those of the buffer. -/
theorem gb_cand {s₀ : State} {K h off count t : Nat} (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s : State} (hI : GB σ s₀ K h off count t s) :
    ∀ l < 2, Vec.CandOf (s.mem.readW (s.gpr .rsi) 256) (gOf σ K h off t) l := by
  obtain hrsi : s.gpr .rsi = at' σ (oBuf + 504 * K + 3 * (off + t)) := by rw [hI.rsi, at', at', Offset.add_add]
  obtain hbyte : ∀ i < 24, byteY (s.mem.readW (s.gpr .rsi) 256) i = (Xb σ K).getD (3 * (168 * h + off + t) + i) 0 :=
    fun i hi => by
      rw [byteY, byte_readW _ _ (by omega_using [hi]), hrsi, at', Offset.add_add, ← at',
        show oBuf + 504 * K + 3 * (off + t) + i = oBuf + 504 * K + (3 * (off + t) + i) by omega_using [],
        hI.out _ (by omega_using [ht, hi]), Xb_getD σ K (by omega_using [hh, hspan, ht, hi])]
      congr 1; omega_using []
  intro l hl i hi
  simp only [Vec.candK, Vec.candG, gOf]
  rw [hbyte _ (by omega_using [hl, hi]), hbyte _ (by omega_using [hl, hi]), hbyte _ (by omega_using [hl, hi])]

/-- The candidates of eight iterations and their masks. -/
theorem vec1_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) (ht : t + 8 ≤ count)
    {s : State} (hI : GB σ s₀ K h off count t s) (hl : (Lt σ K (168 * h + off + t)).length ≤ 248) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.Rej5.vcand) s fun s₁ =>
      VI σ s₀ K h off count t s₁ ∧ s₁.gpr .r10 = s.gpr .r10 := by
  obtain hrsi : s.gpr .rsi = at' σ (oBuf + 504 * K + 3 * (off + t)) := by rw [hI.rsi, at', at', Offset.add_add]
  obtain hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 32 := by
    rw [hrsi]; exact in_scr' hp hI.env.rd hI.env.wr (by simp only [oBuf]; omega_using [hK, hspan, ht])
  exact WP.mono (Vec.vcand_ok (hI.vec hl).1 hin) fun s₁ h₁ => ⟨⟨s, hI, hl, h₁⟩, h₁.2.2.2.2.2.2.2 _ (by decide)⟩

/-- After `vcand` and `vputA`, at iteration `t` with room for eight coefficients. -/
def VP (σ s₀ : State) (K h off count t : Nat) (s₂ : State) : Prop :=
  ∃ s s₁, GB σ s₀ K h off count t s ∧ (Lt σ K (168 * h + off + t)).length ≤ 248 ∧ VIF s s₁ ∧
    Vec.VPA (s.mem.readW (s.gpr .rsi) 256) s₁ s₂

/-- The low lane's coefficients, after `vcand`. -/
theorem vec2a_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) {s₁ : State}
    (hv : VI σ s₀ K h off count t s₁) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.Rej5.vputA) s₁ fun s₂ => VP σ s₀ K h off count t s₂ ∧ s₂.gpr .r10 = s₁.gpr .r10 := by
  obtain ⟨s, hI, hl, hf⟩ := hv
  obtain ⟨hax, h0, c₁, m₁, rd₁, wr₁, sy₁, g₁⟩ := id hf
  obtain hdi : (s₁.gpr .rdi).toNat = (Lt σ K (168 * h + off + t)).length := by
    rw [g₁ _ (by decide), hI.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl])]
  obtain hbp : s₁.gpr .rbp = Proof.MlKem.poly4 (aP σ) K := by rw [g₁ _ (by decide), hI.rbp]
  obtain env₁ : EnvK σ s₁ := hI.env.keep m₁ (show Keep [.rax] s s₁ from ⟨fun r hr => g₁ r (by intro e; subst e; simp at hr), rd₁, wr₁⟩)
    (by decide)
  exact WP.mono (Vec.vputA_ok c₁ h0 hax (by rw [g₁ _ (by decide), sy₁]; exact (hI.vec hl).2) (by rw [hdi]; omega_using [hl])
    (by rw [hbp, hdi]; exact out_reg hp hK env₁ (by omega_using [hl])))
    fun s₂ hv => ⟨⟨s, s₁, hI, hl, hf, hv⟩, hv.gpr _ (by decide) (by decide) (by decide)⟩

/-- The high lane's coefficients, after `vputA`. -/
theorem vec2b_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s₂ : State} (hv : VP σ s₀ K h off count t s₂) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.Rej5.vputB) s₂ fun s' =>
      GB σ s₀ K h off count (t + 8) s' ∧ s'.gpr .r10 = s₂.gpr .r10 := by
  obtain ⟨s, s₁, hI, hl, ⟨hax, h0, c₁, m₁, rd₁, wr₁, sy₁, g₁⟩, hpa⟩ := hv
  obtain hc := gb_cand hh hspan ht hI
  generalize hX : s.mem.readW (s.gpr .rsi) 256 = X at hax h0 hc hpa
  obtain hdi : (s₁.gpr .rdi).toNat = (Lt σ K (168 * h + off + t)).length := by
    rw [g₁ _ (by decide), hI.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl])]
  obtain hbp : s₁.gpr .rbp = Proof.MlKem.poly4 (aP σ) K := by rw [g₁ _ (by decide), hI.rbp]
  obtain e0 := Vec.cntL_eq (hc 0 (by decide))
  obtain e1 := Vec.cntL_eq (hc 1 (by decide))
  obtain hA0 : (Vec.accG (gOf σ K h off t) 0).length ≤ 4 := by rw [← e0]; exact Vec.cntL_le X 0
  obtain hA1 : (Vec.accG (gOf σ K h off t) 1).length ≤ 4 := by rw [← e1]; exact Vec.cntL_le X 1
  obtain env₁ : EnvK σ s₁ := hI.env.keep m₁ (show Keep [.rax] s s₁ from ⟨fun r hr => g₁ r (by intro e; subst e; simp at hr), rd₁, wr₁⟩)
    (by decide)
  refine WP.mono (Vec.vputB_ok hpa (by rw [g₁ _ (by decide), sy₁]; exact (hI.vec hl).2) (by rw [hdi]; omega_using [hl])
    (by rw [hbp, hdi]; exact out_reg hp hK env₁ (by have := Vec.cntL_le X 0; omega_using [hl, this])))
    fun s₂ ⟨hm₂, hdi₂, hsi₂, c₂, rd₂, wr₂, sy₂, g₂⟩ => ?_
  rw [hbp, hdi, m₁] at hm₂
  rw [hdi, e0, e1] at hdi₂
  obtain hL8 : Lt σ K (168 * h + off + (t + 8)) = Lt σ K (168 * h + off + t) ++
      Vec.accG (gOf σ K h off t) 0 ++ Vec.accG (gOf σ K h off t) 1 := by
    rw [← Nat.add_assoc, Lt_steps σ K _ 8 (by omega_using [hh, hspan, ht]), Vec.stepsG_eight (by simp only [Spec.MlDsa.n]; omega_using [hl])]
  obtain st0 := Vec.stored_write4 hI.stored (by omega_using [hl]) hA0 (Vec.compD X 0)
    (fun i hi => Vec.comp_dwords (by decide) (hc 0 (by decide)) i hi)
  obtain st1 := Vec.stored_write4 st0 (by rw [List.length_append]; omega_using [hl, hA0]) hA1 (Vec.compD X 1)
    (fun i hi => Vec.comp_dwords (by decide) (hc 1 (by decide)) i hi)
  rw [List.length_append, ← e0] at st1
  obtain hf : Frame [pR (Proof.MlKem.poly4 (aP σ) K)] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hl]) (by omega_using [hl]))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by have := Vec.cntL_le X 0; omega_using [hl, this]) (by omega_using [hl, e0, hA0]))
  obtain gk : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₂ r h1 h2 h3 h4, g₁ r h1]
  obtain k₂ : Keep [.rax, .rdx, .rdi, .rsi] s s₂ := ⟨fun r hr => gk r (by intro e; subst e; simp at hr)
    (by intro e; subst e; simp at hr) (by intro e; subst e; simp at hr) (by intro e; subst e; simp at hr),
    rd₂.trans rd₁, wr₂.trans wr₁⟩
  refine ⟨⟨env_poly hp hK hI.env hf (rd₂.trans rd₁) (wr₂.trans wr₁) (fun r hr => gk r ?_ ?_ ?_ ?_), ?_, ?_,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), hI.rbp],
    fun p hp' => by
      rw [frame_byte hf (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega_using [hK, hspan, hp']))
        (Region.contains_self _ _)]
      exact hI.out p hp',
    by rw [hL8, hm₂]; exact st1, hI.fr.trans hf, (hI.kp.trans k₂).mono (by simp),
    fun _ => ⟨c₂, by rw [gk _ (by decide) (by decide) (by decide) (by decide), sy₂, sy₁]; exact (hI.vec hl).2⟩⟩,
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), hpa.gpr _ (by decide) (by decide) (by decide)]⟩
  all_goals try (simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [hsi₂, g₁ _ (by decide), hI.rsi, show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, Offset.add_add]
    exact congrArg (fun x => at' σ (oBuf + 504 * K) + BitVec.ofNat 64 x) (by omega_using [])
  · rw [hL8]
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_append, BitVec.toNat_ofNat]
    rw [hdi₂]
    have := Lt_length_le σ K (168 * h + off + (t + 8))
    rw [hL8] at this
    simp only [List.length_append] at this
    omega_using [hl, hA0, hA1]


/-- The stores of eight iterations' coefficients, after `vcand`. -/
theorem vec2_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s₁ : State} (hv : VI σ s₀ K h off count t s₁) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.Rej5.vput) s₁ fun s' =>
      GB σ s₀ K h off count (t + 8) s' ∧ s'.gpr .r10 = s₁.gpr .r10 := by
  rw [show VG.Impl.MlDsa.X86_64.Sample.Rej5.vput = VG.Impl.MlDsa.X86_64.Sample.Rej5.vputA ++ VG.Impl.MlDsa.X86_64.Sample.Rej5.vputB from rfl, WP.block_append_iff]
  exact WP.mono (vec2a_ok hp hK hv) fun s₂ ⟨hv', g₂⟩ =>
    WP.mono (vec2b_ok hp hK hh hspan ht hv') fun s' ⟨h', g'⟩ => ⟨h', by rw [g', g₂]⟩

/-- Eight iterations with the vector code, with room for eight coefficients. -/
theorem gvec_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s : State} (hI : GB σ s₀ K h off count t s)
    (hl : (Lt σ K (168 * h + off + t)).length ≤ 248) :
    WP isa (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.vcand ++ VG.Impl.MlDsa.X86_64.Sample.Rej5.vput)) s fun s' =>
      GB σ s₀ K h off count (t + 8) s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  rw [WP.block_append_iff]
  exact WP.mono (vec1_ok hp hK hspan ht hI hl) fun s₁ ⟨hv, g₁⟩ =>
    WP.mono (vec2_ok hp hK hh hspan ht hv) fun s' ⟨h', g'⟩ => ⟨h', by rw [g', g₁]⟩

omit hp in
theorem cmp249_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 249)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 249)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ x l, s'.lane x l = s.lane x l := by
  xrun [show BitVec.signExtend 64 (249 : BitVec 32) = 249 by decide, show (249 : BitVec 64).toNat = 249 from rfl]
  exact fun _ _ => rfl

omit hp in
theorem sub10_ok (s : State) :
    WP isa (.block [.alu .sub .r10 (.imm 1)]) s fun s' => (s'.mem = s.mem ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some (s.gpr .r10 - 1 == 0) ∧ ∀ x l, s'.lane x l = s.lane x l) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun
  exact fun _ _ => rfl

/-- Eight candidates: with AVX2 or with the scalar loop, then `r10` counts down. -/
theorem vgrp_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s : State} (hI : GB σ s₀ K h off count t s) :
    WP isa VG.Impl.MlDsa.X86_64.Sample.Rej5.vgrp s fun s' => GB σ s₀ K h off count (t + 8) s' ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some (s.gpr .r10 - 1 == 0) := by
  refine WP.seq (WP.mono_syms (cmp249_ok s) fun s₁ ⟨hcf, hm, hg, hrd, hwr, hl⟩ sy => ?_)
  obtain l₁ : GB σ s₀ K h off count t s₁ := hI.same hg hm hrd hwr sy hl
  obtain hlen := Lt_length_le σ K (168 * h + off + t)
  rw [hI.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlen])] at hcf
  refine WP.seq (WP.mono (WP.ite _ hcf (fun hb => gvec_ok hp hK hh hspan ht l₁ (by have := of_decide_eq_true hb; omega_using [this]))
    fun hb => gsca_ok hp hK hh hspan ht l₁ (by have := of_decide_eq_false hb; omega_using [this]))
    fun s₂ ⟨h₂, g₂⟩ => WP.mono_syms (sub10_ok s₂) fun s₃ ⟨⟨hm₃, h10, hz, hl₃⟩, k₃⟩ sy₃ => ?_)
  refine ⟨⟨h₂.env.keep hm₃ k₃ (by decide), by rw [k₃.gpr (by decide), h₂.rsi], by rw [k₃.gpr (by decide), h₂.rdi],
    by rw [k₃.gpr (by decide), h₂.rbp], by rw [hm₃]; exact h₂.out, by rw [hm₃]; exact h₂.stored,
    by rw [hm₃]; exact h₂.fr, (h₂.kp.trans k₃).mono (by simp),
    fun h' => ⟨(h₂.vec h').1.same hl₃, by rw [k₃.gpr (by decide), sy₃]; exact (h₂.vec h').2⟩⟩, by rw [h10, g₂, hg], by rw [hz, g₂, hg]⟩

/-- The setup of a segment: its pointers, the static's address and its constants. -/
theorem setup_ok {K h off count : Nat} (hK : K < 4) (hspan : off + count ≤ 168)
    {s : State} (hI : HPre σ K h off count s) :
    WP isa (.block (setup K off count)) s fun s' => GB σ s K h off count 0 s' ∧
      s'.gpr .r10 = BitVec.ofNat 64 (count / 8) := by
  have hin : InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 :=
    in_scr' hp hI.env.rd hI.env.wr (by simp only [oJ]; omega_using [hK])
  have hsx : BitVec.signExtend 64 (BitVec.ofNat 32 (oBuf + 504 * K + 3 * off)) =
      BitVec.ofNat 64 (oBuf + 504 * K + 3 * off) := sx_ofNat (by simp only [oBuf]; omega_using [hK, hspan])
  have hc : BitVec.setWidth 64 (BitVec.ofNat 32 (count / 8)) = BitVec.ofNat 64 (count / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hspan]
  rw [show setup K off count = [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K + 3 * off))),
      .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
      .mov .rdi (.mem (at_ .rbx (oJ + 8 * K))), .mov32 .r10 (.imm (BitVec.ofNat 32 (count / 8)))] ++
      ([.leaSym .r11 VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName] ++ [.vmovdquTbl .xmm8 (at_ .r11 VG.Impl.MlDsa.X86_64.Sample.Rej5.oCst) VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName VG.Impl.MlDsa.X86_64.Sample.Rej5.tblWords,
      .vmovdquTbl .xmm9 (at_ .r11 (VG.Impl.MlDsa.X86_64.Sample.Rej5.oCst + 32)) VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName VG.Impl.MlDsa.X86_64.Sample.Rej5.tblWords,
      .vmovdquTbl .xmm10 (at_ .r11 (VG.Impl.MlDsa.X86_64.Sample.Rej5.oCst + 64)) VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName VG.Impl.MlDsa.X86_64.Sample.Rej5.tblWords,
      .vmovdquTbl .xmm11 (at_ .r11 (VG.Impl.MlDsa.X86_64.Sample.Rej5.oCst + 96)) VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName VG.Impl.MlDsa.X86_64.Sample.Rej5.tblWords]) from rfl, WP.block_append_iff]
  refine WP.mono_syms (WP.keep [.rsi, .rbp, .rdi, .r10] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K + 3 * off) ∧ s'.gpr .rbp = Proof.MlKem.poly4 (aP σ) K ∧
      s'.gpr .rdi = BitVec.ofNat 64 (Lt σ K (168 * h + off)).length ∧ s'.gpr .r10 = BitVec.ofNat 64 (count / 8) ∧
      ∀ x l, s'.lane x l = s.lane x l)
    (by
      xrun [hI.env.rbx, hI.env.r13, hsx, sxP hK, hin, hI.j, hc]
      exact ⟨rfl, fun _ _ => rfl⟩)
    rfl) fun s₁ ⟨⟨hm, hsi, hbp, hdi, h10, _⟩, k₁⟩ sy₁ => ?_
  rw [WP.block_append_iff]
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩
  generalize hs₂ : s₁.setReg .r11 (s₁.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName) = s₂
  have g₂ : ∀ r, r ≠ .r11 → s₂.gpr r = s₁.gpr r := fun r hr => by
    rw [← hs₂]; exact RegUpd.gpr_setReg_of_ne _ _ hr
  have t₂ : s₂.gpr .r11 = s₂.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName := by rw [← hs₂]; exact RegUpd.gpr_setReg_self _ _ _
  have eaT : ∀ (st : State) (d : Nat), d < 2 ^ 64 → st.gpr .r11 = st.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName →
      (st.ea (at_ .r11 d) - st.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName).toNat = d := fun st d hd hst => by
    rw [VG.Proof.MlKem.X86_64.ea_at, hst, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hlen := Vec.tblWords_length
  refine wp_vtbl (o := 32) t₂ (by rw [eaT _ _ (by decide) t₂]; rfl) (by rw [hlen]; decide) fun s₃ u₃ => ?_
  have t₃ : s₃.gpr .r11 = s₃.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName := by rw [u₃.gpr, u₃.syms]; exact t₂
  refine wp_vtbl (o := 36) t₃ (by rw [eaT _ _ (by decide) t₃]; rfl) (by rw [hlen]; decide) fun s₄ u₄ => ?_
  have t₄ : s₄.gpr .r11 = s₄.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName := by rw [u₄.gpr, u₄.syms]; exact t₃
  refine wp_vtbl (o := 40) t₄ (by rw [eaT _ _ (by decide) t₄]; rfl) (by rw [hlen]; decide) fun s₅ u₅ => ?_
  have t₅ : s₅.gpr .r11 = s₅.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName := by rw [u₅.gpr, u₅.syms]; exact t₄
  refine wp_vtbl (o := 44) t₅ (by rw [eaT _ _ (by decide) t₅]; rfl) (by rw [hlen]; decide) fun s₆ u₆ => WP.block_nil ?_
  obtain ⟨⟨c0, c1⟩, ⟨c2, c3⟩, ⟨c4, c5⟩, ⟨c6, c7⟩⟩ := Vec.cst_vals
  have cst : ∀ {n : Nat}, 32 ≤ n → n < 48 → VG.Impl.MlDsa.X86_64.Sample.Rej5.tblWords.getD n 0 =
      VG.Impl.MlDsa.X86_64.Sample.Rej5.consts.getD (n - 32) 0 := fun h1 h2 => Vec.tblWords_cst' h1 h2
  have vc : Vec.VC s₆ := ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  rotate_left
  · rw [u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl, u₄.other _ (by decide) l hl, u₃.val l hl]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ite_eq_left rfl, cst (by decide) (by decide), cst (by decide) (by decide)]; exact c0
    · rw [ite_eq_right (by decide), cst (by decide) (by decide), cst (by decide) (by decide)]; exact c1
  · rw [u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl, u₄.val l hl]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ite_eq_left rfl, cst (by decide) (by decide), cst (by decide) (by decide)]; exact c2
    · rw [ite_eq_right (by decide), cst (by decide) (by decide), cst (by decide) (by decide)]; exact c3
  · rw [u₆.other _ (by decide) l hl, u₅.val l hl]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ite_eq_left rfl, cst (by decide) (by decide), cst (by decide) (by decide)]; exact c4
    · rw [ite_eq_right (by decide), cst (by decide) (by decide), cst (by decide) (by decide)]; exact c5
  · rw [u₆.val l hl]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ite_eq_left rfl, cst (by decide) (by decide), cst (by decide) (by decide)]; exact c6
    · rw [ite_eq_right (by decide), cst (by decide) (by decide), cst (by decide) (by decide)]; exact c7
  have g6 : ∀ r, r ≠ .r11 → s₆.gpr r = s₁.gpr r := fun r hr => by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, g₂ r hr]
  have m6 : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, ← hs₂, RegUpd.mem_setReg, hm]
  have rd6 : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, ← hs₂, RegUpd.rd_setReg, k₁.2.1]
  have wr6 : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, ← hs₂, RegUpd.wr_setReg, k₁.2.2]
  have t6 : s₆.gpr .r11 = s₆.syms VG.Impl.MlDsa.X86_64.Sample.Rej5.tblName := by rw [u₆.gpr, u₆.syms]; exact t₅
  have k6 : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp, .r10, .r11] s s₆ := ⟨fun r hr => by
    rw [g6 r (by intro e; subst e; simp at hr), k₁.gpr (by intro e; simp at e; rcases e with rfl | rfl | rfl | rfl <;> simp at hr)],
    rd6, wr6⟩
  refine ⟨⟨hI.env.keep m6 k6 (by decide), ?_, ?_, ?_, by rw [m6]; exact hI.out, ?_, by rw [m6]; exact Frame.refl _ _,
    k6, fun _ => ⟨vc, t6⟩⟩, by rw [g6 _ (by decide), h10]⟩
  · rw [g6 _ (by decide), hsi, at', at', Offset.add_add, Nat.add_zero]
  · rw [g6 _ (by decide), hdi, Nat.add_zero]
  · rw [g6 _ (by decide), hbp]
  · rw [m6, Nat.add_zero]; exact hI.stored

theorem parse_ok {K h off count : Nat} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (h8 : count % 8 = 0) {s : State} (hI : HPre σ K h off count s) :
    WP isa (parse K off count) s (GB σ s K h off count count) := by
  refine WP.seq (WP.mono (setup_ok hp hK hspan hI) fun s₁ ⟨h₁, h10⟩ => ?_)
  refine wp_countdown (cnt := .r10) (N := count / 8) (by omega_using [hspan]) (by omega_using [hpos, h8])
    (fun i u => GB σ s K h off count (8 * i) u) (fun i hi u hu _ => ?_) (fun _ h => ?_) (by simpa using h₁) h10
  · exact WP.mono (vgrp_ok hp hK hh hspan (by omega_using [hi]) hu) fun u' ⟨hu', h10', hz⟩ =>
      ⟨by rw [show 8 * i + 8 = 8 * (i + 1) by omega_using []] at hu'; exact hu', h10', hz⟩
  · rwa [show 8 * (count / 8) = count by omega_using [h8]] at h

end
end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end


@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlDsa (Zq G)
open VG.Proof.MlDsa (PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (segment batch)

/-- Parsing a segment of the second buffer, retaining the squeeze state. -/
structure Batch (σ : State) (n off count K : Nat) (s : State) : Prop where
  sq : SqT σ 3 n s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 =
    BitVec.ofNat 64 (Lt σ k (if k < K then 168 + off + count else 168 + off)).length
  st : ∀ k < 4, Stored s.mem (Proof.MlKem.poly4 (aP σ) k)
    (Lt σ k (if k < K then 168 + off + count else 168 + off))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem hpre {n off count K : Nat} (hK : K < 4) (hbuf : 3 * (off + count) ≤ 168 * n)
    {s : State} (h : Batch σ n off count K s) : HPre σ K 1 off count s :=
  ⟨h.sq.env, fun p hp' => by simpa using h.sq.buf K hK p (by omega_using [hbuf, hp']),
    by simpa only [Nat.mul_one, ite_eq_right (Nat.lt_irrefl K)] using h.j K hK,
    by simpa only [Nat.mul_one, ite_eq_right (Nat.lt_irrefl K)] using h.st K hK⟩

/-- Save the count after one segment, preserving the other polynomials and squeeze state. -/
theorem segmentEnd_ok {n off count K : Nat} (hn : n ≤ 3) (hK : K < 4) {s s₁ : State} (h : Batch σ n off count K s) (hA : GB σ s K 1 off count count s₁) :
    WP isa (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) s₁ (Batch σ n off count (K + 1)) := by
  obtain hin : InRegions s₁.wr (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 := in_scr hp hA.env.wr (by simp only [oJ]; omega_using [hK])
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s₁.mem.writeW (at' σ (oJ + 8 * K)) (s₁.gpr .rdi))
    (by xrun [hA.env.rbx, hin]) rfl) fun s₂ ⟨hm, k⟩ => ?_
  obtain hf₂ : Frame [jR σ] s₁.mem s₂.mem := by
    rw [hm]; exact jR_write hK (Frame.refl _ _) _
  obtain k₁ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₁.gpr r = s.gpr r := fun r hr =>
    hA.kp.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨sqT_frame hn (sqT_frame hn h.sq hA.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp hK)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_poly hp hK) (sub_polyR hK) hA.kp.2.1 hA.kp.2.2 k₁)
    hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_jR) sub_jR k.2.1 k.2.2 fun r hr => k.gpr (by simp),
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm]
    by_cases e : k = K
    · subst e
      rw [Mem.readW_writeW_self64, hA.rdi, ite_eq_left (by omega_using []), Nat.mul_one]
    · rw [rd64_off (by simp only [oJ]; omega_using [hk]) (by simp only [oJ]; omega_using [hK]) (by omega_using [e]), j_poly hp hK hA.fr hk, h.j k hk]
      congr 3
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega_using [hk'])]
      · rw [ite_eq_right hk', ite_eq_right (by omega_using [e, hk'])]
  · have hL := Lt_length_le σ k (if k < K + 1 then 168 + off + count else 168 + off)
    refine stored_frame hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact poly_jR hp k hk) ?_ hL
    by_cases e : k = K
    · subst e
      rw [ite_eq_left (by omega_using [])]
      simpa only [Nat.mul_one] using hA.stored
    · have := st_poly hK hk e hA.fr (h.st k hk) (Lt_length_le σ k _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega_using [hk'])]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega_using [e, hk'])]

theorem segment_ok {n off count K : Nat} (hn : n ≤ 3) (hK : K < 4)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (h8 : count % 8 = 0) (hbuf : 3 * (off + count) ≤ 168 * n)
    {s : State} (h : Batch σ n off count K s) :
    WP isa (segment K off count) s (Batch σ n off count (K + 1)) :=
  WP.seq (WP.mono (parse_ok hp hK (by decide) hspan hpos h8 (hpre hK hbuf h))
    fun _ hA => segmentEnd_ok hp hn hK h hA)

theorem batch_ok {n off count : Nat} (hn : n ≤ 3)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (h8 : count % 8 = 0) (hbuf : 3 * (off + count) ≤ 168 * n)
    {s : State} (h : Batch σ n off count 0 s) :
    WP isa (batch off count) s (Batch σ n off count 4) :=
  WP.seq (WP.mono (segment_ok hp hn (by decide) hspan hpos h8 hbuf h) fun _ h₁ =>
    WP.seq (WP.mono (segment_ok hp hn (by decide) hspan hpos h8 hbuf h₁) fun _ h₂ =>
      WP.seq (WP.mono (segment_ok hp hn (by decide) hspan hpos h8 hbuf h₂) fun _ h₃ =>
        segment_ok hp hn (by decide) hspan hpos h8 hbuf h₃)))

omit hp in
theorem batch_of_m2 {s : State} (h : M2 σ 2 s) : Batch σ 2 0 112 0 s :=
  ⟨h.sq, by simpa using h.j, by simpa using h.st⟩

/-- Start the sixth-block parse with the coefficients retained after five. -/
theorem squeeze_last_ok {fast : Bool} {s : State} (h : Batch σ 2 0 112 4 s) :
    WP isa (squeezes 2 1 fast) s (Batch σ 3 112 56 0) := by
  refine WP.mono (sqTs_ok (fast := fast) hp (by decide) (by decide) h.sq) fun s' ⟨q, hf⟩ => ⟨q, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oJ + 8 * k) (n := 8)
        (by simp only [oSave, oJ]; omega_using []) (by simp only [oJ]; omega_using [hk])).symm) (by decide), h.j k hk]
    simp only [ite_eq_left hk, Nat.add_zero, ite_eq_right (Nat.not_lt_zero k)]
  · have st := stored_frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_poly hp hk).symm)
      (h.st k hk) (Lt_length_le σ k _)
    simpa only [ite_eq_left hk, Nat.add_zero, ite_eq_right (Nat.not_lt_zero k)] using st

/-! ## The first 168 candidates of each seed -/

omit hp in
theorem hpre0 {K : Nat} (hK : K < 4) {s : State} (h : P1 σ K s) : HPre σ K 0 0 168 s :=
  ⟨h.sq.env, fun p hp' => by rw [h.sq.buf K hK p (by omega_using [hp'])],
    by rw [h.j K hK, ite_eq_right (by omega_using [])],
    by have := h.st K hK; rw [ite_eq_right (by omega_using [])] at this; exact this⟩

/-- `j` kept, after the first 168 candidates of seed `K`. -/
theorem segment0End_ok {K : Nat} (hK : K < 4) {s s₁ : State} (h : P1 σ K s) (hA : GB σ s K 0 0 168 168 s₁) :
    WP isa (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) s₁ (P1 σ (K + 1)) := by
  obtain hin : InRegions s₁.wr (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 := in_scr hp hA.env.wr (by simp only [oJ]; omega_using [hK])
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s₁.mem.writeW (at' σ (oJ + 8 * K)) (s₁.gpr .rdi))
    (by xrun [hA.env.rbx, hin]) rfl) fun s₂ ⟨hm, k⟩ => ?_
  obtain hf₂ : Frame [jR σ] s₁.mem s₂.mem := by
    rw [hm]; exact jR_write hK (Frame.refl _ _) _
  obtain k₁ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₁.gpr r = s.gpr r := fun r hr =>
    hA.kp.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨sqT_frame (by decide) (sqT_frame (by decide) h.sq hA.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp hK)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_poly hp hK) (sub_polyR hK) hA.kp.2.1 hA.kp.2.2 k₁)
    hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_jR) sub_jR k.2.1 k.2.2 fun r hr => k.gpr (by simp),
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm]
    by_cases e : k = K
    · subst e
      rw [Mem.readW_writeW_self64, hA.rdi, ite_eq_left (by omega_using [])]
    · rw [rd64_off (by simp only [oJ]; omega_using [hk]) (by simp only [oJ]; omega_using [hK]) (by omega_using [e]), j_poly hp hK hA.fr hk, h.j k hk]
      congr 3
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega_using [hk'])]
      · rw [ite_eq_right hk', ite_eq_right (by omega_using [e, hk'])]
  · have hL := Lt_length_le σ k (if k < K + 1 then 168 else 0)
    refine stored_frame hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact poly_jR hp k hk) ?_ hL
    by_cases e : k = K
    · subst e
      rw [ite_eq_left (by omega_using [])]
      exact hA.stored
    · have := st_poly hK hk e hA.fr (h.st k hk) (Lt_length_le σ k _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega_using [hk'])]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega_using [e, hk'])]

/-- The first 168 candidates of seed `K`. -/
theorem segment0_ok {K : Nat} (hK : K < 4) {s : State} (h : P1 σ K s) : WP isa (segment K 0 168) s (P1 σ (K + 1)) :=
  WP.seq (WP.mono (parse_ok hp hK (by decide) (by decide) (by decide) (by decide) (hpre0 hK h))
    fun _ hA => segment0End_ok hp hK h hA)

end
end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end

/-! ### `MlDsa.X86_64.Sample.Rej5ParseCT`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep Keep WP.keep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct RX relInvX bsum bsum_congr)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (parse segment batch)

/-- Two runs at iteration `t` of a half of seed `K`, from states with `X`,
`n = count - t` iterations from its end. -/
def HI (X : State → State → Prop) (K h off count n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ s₀₁ s₀₂ t, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = count - t ∧ t < count ∧
    X σ₁ s₀₁ ∧ X σ₂ s₀₂ ∧ HAt σ₁ s₀₁ K h off count t s₁ ∧ HAt σ₂ s₀₂ K h off count t s₂

theorem hbpre {σ : State} (hp : Pre σ) {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) (ht : t < count) {s : State}
    (hI : HAt σ s₀ K h off count t s) : BPre s (Proof.MlKem.poly4 (aP σ) K) (Lt σ K (168 * h + off + t)) :=
  ⟨hI.rbp, hI.rdi, Lt_length_le σ K _, coeffsWr hp hK hI.env, hI.stored,
    by simpa using hat_regions hp hK hspan hI (j := 0) (by omega_using [ht]), hat_regions hp hK hspan hI (by omega_using [ht]),
    hat_regions hp hK hspan hI (by omega_using [ht])⟩

theorem hi_brel {X : State → State → Prop} {K h off count n : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) {s₁ s₂ : State}
    (H : HI X K h off count n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, _, ht, _, _, l₁, l₂⟩ := H
  refine ⟨Proof.MlKem.poly4 (aP σ₁) K, Lt σ₁ K (168 * h + off + t), hbpre (pre_of p₁) hK hspan ht l₁,
    by rw [pub_aP hq, pub_Lt4 hq hK]; exact hbpre (pre_of p₂) hK hspan ht l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [hat_byte hh hspan l₁ (by omega_using [ht, hk]), hat_byte hh hspan l₂ (by omega_using [ht, hk])]
  simp only [Xb, pub_B hq hK]

/-- The loop of a half. -/
theorem hloop_ct {X : State → State → Prop} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (n : Nat) :
    RelCT isa (HI X K h off count n) (.loop rnBody .ne) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h off count count s) := by
  refine RelCT.loop (M := isa) (HI X K h off count) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × State × Nat, sample4K.pre p.1 ∧ p.2.2 < count ∧
      HAt p.1 p.2.1 K h off count p.2.2 x →
        HAt p.1 p.2.1 K h off count (p.2.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (count - p.2.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y H => hi_brel hK hh hspan H) fun _ _ _ => trivial) (fun x y H => ?_) ?_
  · obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, _, _, ht, _, _, l₁, l₂⟩ := H
    exact ⟨WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hspan hp'.2.1 hp'.2.2) ⟨(σ₁, s₀₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hspan hp'.2.1 hp'.2.2) ⟨(σ₂, s₀₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, hn, ht, x₁, x₂, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, s₀₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, s₀₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (count - t) - 1 == 0) = decide (t + 1 = count) := by
      rw [ofNat64_pred (by omega_using [ht]) (by omega_using [hspan]), ofNat64_beq_zero (by omega_using [hspan])]
      exact decide_eq_decide.mpr (by omega_using [ht])
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = count := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁'⟩, ⟨s₀₂, x₂, l₂'⟩⟩
    · have : t + 1 ≠ count := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨count - (t + 1), by omega_using [hn, ht], σ₁, σ₂, s₀₁, s₀₂, t + 1, p₁, p₂, hq, rfl, by omega_using [ht, this], x₁, x₂, l₁', l₂'⟩

/-! ## Groups of eight candidates -/

/-- Two runs at group `t` of a segment, with `r10 = c`, each from a state with `X`. -/
abbrev RG (X : State → State → Prop) (K h off count t : Nat) (c : BitVec 64) : State → State → Prop :=
  RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ s.gpr .r10 = c

/-- The mask of the candidates less than `q` of lane `l` of the bytes `g`. -/
abbrev maskG (g : Nat → Byte) (l : Nat) : Nat := bsum (fun i => decide (Vec.candG g (4 * l + i) < Spec.MlDsa.q)) 4

theorem maskL_eq {X : BitVec 256} {g : Nat → Byte} {l : Nat} (hc : Vec.CandOf X g l) : Vec.maskL X l = maskG g l :=
  bsum_congr fun i hi => by rw [hc i hi]

/-- The registers `vput` reads, after `vcand`, are the same in both runs. -/
theorem vi_regs {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {s₀₁ s₀₂ : State} {K h off count t : Nat} (hK : K < 4)
    (hh : h < 2) (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) {x y : State}
    (h₁ : VI σ₁ s₀₁ K h off count t x) (h₂ : VI σ₂ s₀₂ K h off count t y) :
    ∀ r ∈ [Reg.rax, .rbp, .rdi, .rsi], x.gpr r = y.gpr r := by
  obtain ⟨u₁, l₁, -, a₁, -, -, -, -, -, -, g₁⟩ := h₁
  obtain ⟨u₂, l₂, -, a₂, -, -, -, -, -, -, g₂⟩ := h₂
  have c₁ := gb_cand hh hspan ht l₁
  have c₂ := gb_cand hh hspan ht l₂
  have ex : Xb σ₁ K = Xb σ₂ K := by unfold Xb; rw [pub_B hq hK]
  have eg : gOf σ₁ K h off t = gOf σ₂ K h off t := by unfold gOf; rw [ex]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    rw [a₁, a₂, maskL_eq (c₁ 0 (by decide)), maskL_eq (c₁ 1 (by decide)), maskL_eq (c₂ 0 (by decide)),
      maskL_eq (c₂ 1 (by decide)), eg]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rbp, l₂.rbp, pub_aP hq]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rdi, l₂.rdi, pub_Lt4 hq hK]
  · rw [g₁ _ (by decide), g₂ _ (by decide), l₁.rsi, l₂.rsi, at', at', pub_scr hq]

/-- The registers `vputB` reads, after `vputA`, are the same in both runs. -/
theorem vp_regs {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {s₀₁ s₀₂ : State} {K h off count t : Nat} (hK : K < 4)
    (hh : h < 2) (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) {x y : State}
    (h₁ : VP σ₁ s₀₁ K h off count t x) (h₂ : VP σ₂ s₀₂ K h off count t y) :
    ∀ r ∈ [Reg.rax, .rbp, .rdi, .rsi], x.gpr r = y.gpr r := by
  obtain ⟨u₁, v₁, l₁, -, f₁, p₁⟩ := h₁
  obtain ⟨u₂, v₂, l₂, -, f₂, p₂⟩ := h₂
  have g₁ := f₁.2.2.2.2.2.2.2
  have g₂ := f₂.2.2.2.2.2.2.2
  have c₁ := gb_cand hh hspan ht l₁
  have c₂ := gb_cand hh hspan ht l₂
  have ex : Xb σ₁ K = Xb σ₂ K := by unfold Xb; rw [pub_B hq hK]
  have eg : gOf σ₁ K h off t = gOf σ₂ K h off t := by unfold gOf; rw [ex]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    rw [p₁.rax, p₂.rax, maskL_eq (c₁ 1 (by decide)), maskL_eq (c₂ 1 (by decide)), eg]
  · rw [p₁.gpr _ (by decide) (by decide) (by decide), p₂.gpr _ (by decide) (by decide) (by decide), g₁ _ (by decide),
      g₂ _ (by decide), l₁.rbp, l₂.rbp, pub_aP hq]
  · apply BitVec.eq_of_toNat_eq
    rw [p₁.rdi, p₂.rdi, g₁ _ (by decide), g₂ _ (by decide), l₁.rdi, l₂.rdi, Vec.cntL_eq (c₁ 0 (by decide)),
      Vec.cntL_eq (c₂ 0 (by decide)), eg, pub_Lt4 hq hK]
  · rw [p₁.gpr _ (by decide) (by decide) (by decide), p₂.gpr _ (by decide) (by decide) (by decide), g₁ _ (by decide),
      g₂ _ (by decide), l₁.rsi, l₂.rsi, at', at', pub_scr hq]

/-- Eight candidates with the vector code. -/
theorem vec_ct {X : State → State → Prop} {K h off count t : Nat} {c : BitVec 64} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) :
    RelCT isa (RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ (Lt σ K (168 * h + off + t)).length ≤ 248 ∧
      s.gpr .r10 = c) (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.vcand ++ (VG.Impl.MlDsa.X86_64.Sample.Rej5.vputA ++ VG.Impl.MlDsa.X86_64.Sample.Rej5.vputB))) (RG X K h off count (t + 8) c) :=
  RelCT.block_append (RelCT.seq
    (relInvX (I' := fun σ s₀ s => VI σ s₀ K h off count t s ∧ s.gpr .r10 = c)
      (fun σ s₀ s hp _ h' => WP.mono (vec1_ok (pre_of hp) hK hspan ht h'.1 h'.2.1) fun _ ⟨hi, h10⟩ =>
        ⟨hi, by rw [h10]; exact h'.2.2⟩)
      (taintRel [.rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rsi, h₂.1.rsi, at', at', pub_scr hq])
        (by taint_decide)))
    (RelCT.block_append (RelCT.seq
      (relInvX (I' := fun σ s₀ s => VP σ s₀ K h off count t s ∧ s.gpr .r10 = c)
        (fun σ s₀ s hp _ h' => WP.mono (vec2a_ok (pre_of hp) hK h'.1) fun _ ⟨hv, h10⟩ =>
          ⟨hv, by rw [h10]; exact h'.2⟩)
        (taintRel [.rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ =>
          vi_regs hq hK hh hspan ht h₁.1 h₂.1) (by taint_decide)))
      (relInvX (fun σ s₀ s hp _ h' => WP.mono (vec2b_ok (pre_of hp) hK hh hspan ht h'.1) fun _ ⟨l, h10⟩ =>
          ⟨l, by rw [h10]; exact h'.2⟩)
        (taintRel [.rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ =>
          vp_regs hq hK hh hspan ht h₁.1 h₂.1) (by taint_decide))))))

/-- The states after `mov ecx, 8` of a group with more than 248 coefficients. -/
def SX (X : State → State → Prop) (K h off count t : Nat) (c : BitVec 64) (σ s₁ : State) : Prop :=
  ∃ s₀ s, X σ s₀ ∧ GB σ s₀ K h off count t s ∧ 248 < (Lt σ K (168 * h + off + t)).length ∧ s.gpr .r10 = c ∧
    s₁.mem = s.mem ∧ Keep [.rcx] s s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 8

/-- Eight candidates with the scalar loop. -/
theorem sca_ct {X : State → State → Prop} {K h off count t : Nat} {c : BitVec 64} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) :
    RelCT isa (RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ 248 < (Lt σ K (168 * h + off + t)).length ∧
      s.gpr .r10 = c) VG.Impl.MlDsa.X86_64.Sample.Rej5.sca8 (RG X K h off count (t + 8) c) := by
  have h₁ : RelCT isa (RX X fun σ s₀ s => GB σ s₀ K h off count t s ∧ 248 < (Lt σ K (168 * h + off + t)).length ∧
      s.gpr .r10 = c) (.block [.mov32 .rcx (.imm 8)]) (R4 (SX X K h off count t c)) :=
    relInv (fun σ s _ ⟨s₀, hx, hI, hl, h10⟩ => WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧
        s'.gpr .rcx = BitVec.ofNat 64 8) (by xrun) rfl) fun s₁ ⟨⟨hm, hc⟩, k⟩ => ⟨s₀, s, hx, hI, hl, h10, hm, k, hc⟩)
      (taintRel [] nil_regs (by taint_decide))
  have h₂ : RelCT isa (HI (SX X K h off count t c) K h (off + t) 8 8) (.loop rnBody .ne)
      (R4 fun σ s => ∃ s₀, SX X K h off count t c σ s₀ ∧ HAt σ s₀ K h (off + t) 8 8 s) :=
    hloop_ct hK hh (by omega_using [hspan, ht]) 8
  show RelCT isa _ (.seq (.block [.mov32 .rcx (.imm 8)]) (.loop rnBody .ne)) _
  refine RelCT.seq (RelCT.mono h₁ (fun _ _ h => h) fun x y hxy => ?_) (RelCT.mono h₂ (fun _ _ h => h) fun x y hxy => ?_)
  · obtain ⟨σ₁, σ₂, p₁, p₂, hq, x₁, x₂⟩ := hxy
    obtain ⟨_, _, _, l₁, _, _, m₁, k₁, c₁⟩ := id x₁
    obtain ⟨_, _, _, l₂, _, _, m₂, k₂, c₂⟩ := id x₂
    exact ⟨σ₁, σ₂, x, y, 0, p₁, p₂, hq, rfl, by decide, x₁, x₂, hat0_of ht l₁ m₁ k₁ c₁, hat0_of ht l₂ m₂ k₂ c₂⟩
  · obtain ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₁, x₁, a₁⟩, ⟨s₂, x₂, a₂⟩⟩ := hxy
    obtain ⟨s₀₁, u₁, y₁, l₁, d₁, r₁, m₁, k₁, -⟩ := x₁
    obtain ⟨s₀₂, u₂, y₂, l₂, d₂, r₂, m₂, k₂, -⟩ := x₂
    obtain ⟨g₁, e₁⟩ := gb_of_hat (pre_of p₁) hK hh hspan ht l₁ m₁ k₁ a₁ d₁
    obtain ⟨g₂, e₂⟩ := gb_of_hat (pre_of p₂) hK hh hspan ht l₂ m₂ k₂ a₂ d₂
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, y₁, g₁, by rw [e₁, r₁]⟩, ⟨s₀₂, y₂, g₂, by rw [e₂, r₂]⟩⟩

/-- A group of eight candidates. -/
theorem vgrp_ct {X : State → State → Prop} {K h off count t : Nat} {c : BitVec 64} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (ht : t + 8 ≤ count) :
    RelCT isa (RG X K h off count t c) VG.Impl.MlDsa.X86_64.Sample.Rej5.vgrp
      (RX X fun σ s₀ s => GB σ s₀ K h off count (t + 8) s ∧ s.gpr .r10 = c - 1 ∧ s.zf = some (c - 1 == 0)) := by
  have hcmp : RelCT isa (RG X K h off count t c) (.block [.alu .cmp .rdi (.imm 249)])
      (RX X fun σ s₀ s => (GB σ s₀ K h off count t s ∧ s.gpr .r10 = c) ∧
        s.cf = some (decide ((Lt σ K (168 * h + off + t)).length < 249))) :=
    relInvX (fun σ s₀ s _ _ h' => by
        have hlen := Lt_length_le σ K (168 * h + off + t)
        refine WP.mono_syms (cmp249_ok s) fun s' ⟨hcf, hm, hg, hrd, hwr, hl⟩ sy => ?_
        exact ⟨⟨h'.1.same hg hm hrd hwr sy hl, by rw [hg]; exact h'.2⟩,
          by rw [hcf, h'.1.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlen])]⟩)
      (taintRel [.rdi] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rdi, h₂.1.rdi, pub_Lt4 hq hK])
        (by taint_decide))
  have hite : RelCT isa (RX X fun σ s₀ s => (GB σ s₀ K h off count t s ∧ s.gpr .r10 = c) ∧
        s.cf = some (decide ((Lt σ K (168 * h + off + t)).length < 249)))
      (.ite .b (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.vcand ++ (VG.Impl.MlDsa.X86_64.Sample.Rej5.vputA ++ VG.Impl.MlDsa.X86_64.Sample.Rej5.vputB))) VG.Impl.MlDsa.X86_64.Sample.Rej5.sca8) (RG X K h off count (t + 8) c) := by
    refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => by
        show x.cf = y.cf; rw [h₁.2, h₂.2, pub_Lt4 hq hK]) ?_ ?_
    · refine RelCT.mono (vec_ct hK hh hspan ht) ?_ fun _ _ h => h
      rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨l₁, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨l₂, d₂⟩, f₂⟩⟩, hb⟩
      have hb₁ : (Lt σ₁ K (168 * h + off + t)).length < 249 := by
        have : x.cf = some true := hb
        rw [f₁] at this; simpa using this
      have hb₂ : (Lt σ₂ K (168 * h + off + t)).length < 249 := by rw [← pub_Lt4 hq hK]; exact hb₁
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, by omega_using [hb₁], d₁⟩, ⟨s₀₂, x₂, l₂, by omega_using [hb₂], d₂⟩⟩
    · refine RelCT.mono (sca_ct hK hh hspan ht) ?_ fun _ _ h => h
      rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, ⟨l₁, d₁⟩, f₁⟩, ⟨s₀₂, x₂, ⟨l₂, d₂⟩, f₂⟩⟩, hb⟩
      have hb₁ : ¬ (Lt σ₁ K (168 * h + off + t)).length < 249 := by
        have : x.cf = some false := hb
        rw [f₁] at this; simpa using this
      have hb₂ : ¬ (Lt σ₂ K (168 * h + off + t)).length < 249 := by rw [← pub_Lt4 hq hK]; exact hb₁
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, by omega_using [hb₁], d₁⟩, ⟨s₀₂, x₂, l₂, by omega_using [hb₂], d₂⟩⟩
  have hsub : RelCT isa (RG X K h off count (t + 8) c) (.block [.alu .sub .r10 (.imm 1)])
      (RX X fun σ s₀ s => GB σ s₀ K h off count (t + 8) s ∧ s.gpr .r10 = c - 1 ∧ s.zf = some (c - 1 == 0)) :=
    relInvX (fun σ s₀ s _ _ h' => WP.mono_syms (sub10_ok s) fun s' ⟨⟨hm, h10, hz, hl⟩, k⟩ sy =>
        ⟨⟨h'.1.env.keep hm k (by decide), by rw [k.gpr (by decide), h'.1.rsi], by rw [k.gpr (by decide), h'.1.rdi],
          by rw [k.gpr (by decide), h'.1.rbp], by rw [hm]; exact h'.1.out, by rw [hm]; exact h'.1.stored,
          by rw [hm]; exact h'.1.fr, (h'.1.kp.trans k).mono (by simp),
          fun hv => ⟨(h'.1.vec hv).1.same hl, by rw [k.gpr (by decide), sy]; exact (h'.1.vec hv).2⟩⟩,
          by rw [h10, h'.2], by rw [hz, h'.2]⟩)
      (taintRel [.r10] (fun x y ⟨σ₁, σ₂, _, _, _, ⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) (by taint_decide))
  exact RelCT.seq hcmp (RelCT.seq hite hsub)

/-- Two runs at group `i` of a loop of `N` groups, `n = N - i` from its end. -/
def LI (X : State → State → Prop) (K h off count N n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ i, n = N - i ∧ i < N ∧ RG X K h off count (8 * i) (BitVec.ofNat 64 (N - i)) s₁ s₂

theorem loop_ct {X : State → State → Prop} {K h off count : Nat} (hK : K < 4) (hh : h < 2)
    (hspan : off + count ≤ 168) (h8 : count % 8 = 0) (n : Nat) :
    RelCT isa (LI X K h off count (count / 8) n) (.loop VG.Impl.MlDsa.X86_64.Sample.Rej5.vgrp .ne)
      (RX X fun σ s₀ s => GB σ s₀ K h off count count s) := by
  refine RelCT.loop (M := isa) (LI X K h off count (count / 8)) (fun n => ?_) n
  refine RelCT.mono (P := fun s₁ s₂ => ∃ i, n = count / 8 - i ∧ i < count / 8 ∧
      RG X K h off count (8 * i) (BitVec.ofNat 64 (count / 8 - i)) s₁ s₂)
    (RelCT.exists_ fun i => ?_) (fun _ _ h => by unfold LI at h; exact h) fun _ _ h => h
  by_cases hi : i < count / 8 ∧ n = count / 8 - i
  · obtain ⟨hi, hn⟩ := hi
    refine RelCT.mono (P := RG X K h off count (8 * i) (BitVec.ofNat 64 (count / 8 - i)))
      (vgrp_ct hK hh hspan (by omega_using [hi]))
      (fun _ _ h => h.2.2) fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁, d₁, z₁⟩, ⟨s₀₂, x₂, l₂, d₂, z₂⟩⟩ => ?_
    rw [ofNat64_pred (by omega_using [hi]) (by omega_using [hspan])] at d₁ d₂ z₁ z₂
    rw [ofNat64_beq_zero (by omega_using [hspan])] at z₁ z₂
    rw [show 8 * i + 8 = 8 * (i + 1) by omega_using []] at l₁ l₂
    refine ⟨by show x.zf.map _ = y.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
    · have : count / 8 - i - 1 = 0 := by
        have : x.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [show 8 * (i + 1) = count by omega_using [h8, hi, this]] at l₁ l₂
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩
    · have : count / 8 - i - 1 ≠ 0 := by
        have : x.zf.map (!·) = some true := ht
        rw [z₁] at this; simpa using this
      exact ⟨count / 8 - (i + 1), by omega_using [hi, hn], i + 1, rfl, by omega_using [this], σ₁, σ₂, p₁, p₂, hq,
        ⟨s₀₁, x₁, l₁, by rw [d₁]; congr 1⟩, ⟨s₀₂, x₂, l₂, by rw [d₂]; congr 1⟩⟩
  · exact RelCT.of_false fun _ _ h => hi ⟨h.2.1, h.1⟩

/-- A segment of seed `K` from states with `X`, given the taint analysis of its setup. -/
theorem parse_ct {X : State → State → Prop} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (hpos : 0 < count) (h8 : count % 8 = 0)
    (hX : ∀ σ s, sample4K.pre σ → X σ s → HPre σ K h off count s) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K off count)) hc).isSome = true) :
    RelCT isa (R4 X) (parse K off count) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ GB σ s₀ K h off count count s) := by
  unfold VG.Impl.MlDsa.X86_64.Sample.Rej5.parse
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => ∃ s₀, X σ s₀ ∧ GB σ s₀ K h off count 0 s ∧
        s.gpr .r10 = BitVec.ofNat 64 (count / 8))
      (fun σ s hp hx => WP.mono (setup_ok (pre_of hp) hK hspan (hX σ s hp hx)) fun _ h' => ⟨s, hx, h'⟩)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ r hr => by
        have e₁ := (hX σ₁ x p₁ h₁).env
        have e₂ := (hX σ₂ y p₂ h₂).env
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq e₁ e₂
        · rw [e₁.r13, e₂.r13, pub_aP hq]) c)) (fun _ _ h => h)
      (Q' := LI X K h off count (count / 8) (count / 8)) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩ =>
        ⟨0, by omega_using [], by omega_using [hpos, h8], σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁.1, by rw [l₁.2]; rfl⟩,
          ⟨s₀₂, x₂, l₂.1, by rw [l₂.2]; rfl⟩⟩)
    (RelCT.mono (loop_ct hK hh hspan h8 (count / 8)) (fun _ _ h => h) fun _ _ h => h)

theorem segment_ct {n off count K : Nat} (hn : n ≤ 3) (hK : K < 4)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (h8 : count % 8 = 0) (hbuf : 3 * (off + count) ≤ 168 * n)
    {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13])
      (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K off count)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (R4 fun σ s => Batch σ n off count K s) (segment K off count)
      (R4 fun σ s => Batch σ n off count (K + 1) s) :=
  RelCT.seq (parse_ct hK (by decide) hspan hpos h8 (fun _ _ _ h => hpre hK hbuf h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => segmentEnd_ok (pre_of hp) hn hK h₀ hA)
      (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.env a₂.env) c₂))

/-- The first 168 candidates of seed `K`, given the taint analysis of their setup and count's store. -/
theorem segment0_ct {K : Nat} (hK : K < 4) {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Impl.MlDsa.X86_64.Sample.Rej5.setup K 0 168)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) h₂).isSome =
      true) :
    RelCT isa (R4 fun σ s => P1 σ K s) (segment K 0 168) (R4 fun σ s => P1 σ (K + 1) s) :=
  RelCT.seq (parse_ct hK (by decide) (by decide) (by decide) (by decide) (fun _ _ _ h => hpre0 hK h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => segment0End_ok (pre_of hp) hK h₀ hA)
      (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.env a₂.env) c₂))

end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end

/-! ### `MlDsa.X86_64.Sample.Rej5Top`, which only this module used -/

section

/-! ### `MlDsa.X86_64.Sample.Rej5Flags`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlDsa (Zq G)
open VG.Proof.MlDsa (PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (segment batch)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (flags)

/-- A saturated rejection fold is unchanged by the sixth block. -/
theorem full_after_five (σ : State) (k : Nat) (h : (Lt σ k 280).length = 256) :
    Lt σ k 336 = Lt σ k 280 := by
  have e : G (B σ k) 1008 = G (B σ k) 840 ++ (G (B σ k) 1008).drop 840 := by
    rw [← VG.Proof.MlDsa.Sample.G_take (B σ k) (by decide : 840 ≤ 1008), List.take_append_drop]
  have hl : Lt σ k 280 = rnFold [] (G (B σ k) 840) := by
    simp only [Lt, show 3 * 280 = 840 by rfl]
    rw [VG.Proof.MlDsa.Sample.G_take _ (by decide)]
  rw [Lt_336, hl, e, VG.Proof.MlDsa.Sample.rnFold_append _ _ _ (by rw [G_length]),
    VG.Proof.MlDsa.Sample.rnFold_full (by rwa [hl] at h)]

def allFull (σ : State) (n : Nat) : Bool :=
  (List.range 4).all fun k => (Lt σ k n).length == 256

section
variable {σ : State} (hp : Pre σ)
include hp

theorem flags_ok {n : Nat} {s : State} (env : EnvK σ s)
    (j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k n).length) :
    WP isa (.block flags) s fun s' =>
      (s'.gpr .r14 = (if allFull σ n then 1 else 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  have hin : ∀ k < 4, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oJ + 8 * k)) 8 :=
    fun k hk => in_scr' hp env.rd env.wr (by simp only [oJ]; omega_using [hk])
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide)
  have h2 := hin 2 (by decide); have h3 := hin 3 (by decide)
  have j0 := j 0 (by decide); have j1 := j 1 (by decide)
  have j2 := j 2 (by decide); have j3 := j 3 (by decide)
  simp only [oJ, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 j0 j1 j2 j3
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  change WP isa (.block ([.mov32 .r14 (.imm 1),
    .mov .rax (.mem (at_ .rbx 4424)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4432)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4440)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4448)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)])) s _
  xrun [env.rbx, h0, h1, h2, h3, j0, j1, j2, j3]
  simp only [full_bit (Lt_length_le σ _ _)]
  unfold allFull
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  cases (Lt σ 0 n).length == 256 <;> cases (Lt σ 1 n).length == 256 <;>
    cases (Lt σ 2 n).length == 256 <;> cases (Lt σ 3 n).length == 256 <;> rfl

end
end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end


@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlDsa (Zq G)
open VG.Proof.MlDsa (PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (flags fallback finish)

structure Done (σ s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ 4)
  st : ∀ k < 4, Stored s.mem (Proof.MlKem.poly4 (aP σ) k) (Lt σ k 336)

theorem Batch.restore {σ s s' : State} {n off count K : Nat} (h : Batch σ n off count K s)
    (hm : s'.mem = s.mem) (hk : Keep [.rax, .r14] s s') (hr : s'.gpr .r14 = 1) : Batch σ n off count K s' :=
  ⟨⟨h.sq.env.keep hm hk (by simp), hr, by rw [hm]; exact h.sq.rc,
    by rw [hm]; exact h.sq.lanes, by rw [hm]; exact h.sq.buf⟩,
    by rw [hm]; exact h.j, by rw [hm]; exact h.st⟩

section
variable {σ : State} (hp : Pre σ)
include hp

/-- The return value, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : Done σ s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega_using [hi])
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    simp only [Lt_336]
    split <;> rfl
  · rw [hm]
    have := h.st k hk
    rw [Lt_336] at this
    exact stored_polyIs this e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega_using [])⟩)
      (by decide)


/-- Clear upper vector lanes before restoring the caller's registers. -/
theorem end_vec_ok {s : State} (h : Done σ s) :
    WP isa (.block (([.vop .vzeroupper] : List Instr) ++ epi)) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  apply WP.block_append
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s.mem) (by xrun; rfl) rfl) fun s' ⟨hm, hk⟩ => ?_
  exact end_ok hp ⟨h.env.keep hm hk (by simp), by rw [hk.gpr (by simp)]; exact h.r14,
    by rw [hm]; exact h.st⟩

theorem last_flags_ok {s : State} (h : Batch σ 3 112 56 4 s) : WP isa (.block flags) s (Done σ) := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 336).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  refine WP.mono (flags_ok hp h.sq.env hj) fun s' ⟨⟨hr, hm⟩, hk⟩ =>
    ⟨h.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_⟩
  · rw [hr]; unfold allFull okN; split <;> rfl
  · rw [hm]; simpa only [ite_eq_left hk'] using h.st k hk'

theorem fallback_ok {fast : Bool} {s s₀ : State} (h : Batch σ 2 0 112 4 s₀)
    (hm : s.mem = s₀.mem) (hk : Keep [.rax, .r14] s₀ s) : WP isa (fallback fast) s (Done σ) := by
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s' ⟨⟨hm', hr⟩, hk'⟩ => ?_)
  have hb := h.restore (hm'.trans hm) ((hk.trans hk').mono (by simp)) hr
  exact WP.seq (WP.mono (squeeze_last_ok (fast := fast) hp hb) fun _ h₁ =>
    WP.seq (WP.mono (batch_ok hp (by decide) (by decide) (by decide) (by decide) (by decide) h₁)
      fun _ h₂ => last_flags_ok hp h₂))

omit hp in
theorem early_done {s s₀ : State} (h : Batch σ 2 0 112 4 s₀)
    (hm : s.mem = s₀.mem) (hk : Keep [.rax, .r14] s₀ s)
    (hr : s.gpr .r14 = 1) (hf : allFull σ 280 = true) : Done σ s := by
  have hfull : ∀ k < 4, (Lt σ k 280).length = 256 := by
    simpa only [allFull, List.all_eq_true, List.mem_range, beq_iff_eq] using hf
  have he : ∀ k < 4, Lt σ k 336 = Lt σ k 280 := fun k hk => full_after_five σ k (hfull k hk)
  refine ⟨h.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_⟩
  · have hf' : (List.range 4).all (fun k => (Lt σ k 336).length == 256) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      intro k hk; rw [he k hk]; exact hfull k hk
    rw [hr, okN, hf']; rfl
  · rw [hm, he k hk']; simpa only [ite_eq_left hk'] using h.st k hk'

theorem finish_ok {fast : Bool} {s : State} (h : Batch σ 2 0 112 4 s) :
    WP isa (finish fast) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  apply WP.seq
  apply WP.block_append
  refine WP.mono (flags_ok hp h.sq.env hj) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  apply WP.seq
  apply WP.mono (Q := Done σ) ?_ (fun _ hd => end_vec_ok hp hd)
  have hkeep : Keep [.rax, .r14] s s₂ := (hk.trans hk').mono (by simp)
  cases hf : allFull σ 280 with
  | false =>
    have hz' : s₂.zf = some true := by rw [hz, hr, hf]; rfl
    exact WP.ite true hz' (fun _ => fallback_ok (fast := fast) hp h (hm'.trans hm) hkeep)
      (fun hb => absurd hb (by decide))
  | true =>
    have hz' : s₂.zf = some false := by rw [hz, hr, hf]; rfl
    refine WP.ite false hz' (fun hb => absurd hb (by decide)) (fun _ => WP.block_nil ?_)
    exact early_done h (hm'.trans hm) hkeep (by rw [hr', hr, hf]; rfl) hf

/-- Everything after the prologue, the round constants and the padded seeds. -/
theorem body_ok {fast : Bool} {s : State} (h : SqInv σ 0 s) :
    WP isa (.seq (squeezes 0 3 fast) (.seq (.block zeroJ)
      (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 0 0 168) (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 1 0 168)
        (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 2 0 168) (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.segment 3 0 168)
        (.seq (squeezes 0 2 fast) (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.batch 0 112) (finish fast))))))))) s
      fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (sqTs_ok (fast := fast) hp (by decide) (by decide) (sqT_of h)) fun s₃ ⟨q₃, _⟩ =>
      WP.seq (WP.mono (zeroJ_ok hp q₃) fun s₄ p₀ => ?_))
  refine WP.seq (WP.mono (segment0_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (segment0_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (segment0_ok hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (segment0_ok hp (by decide) p₃) fun _ p₄ => ?_))))
  exact WP.seq (WP.mono (sqM_ok (fast := fast) hp (by decide) (by decide) (m2_of p₄)) fun _ m₂ =>
      WP.seq (WP.mono (batch_ok hp (by decide) (by decide) (by decide) (by decide) (by decide) (batch_of_m2 m₂))
        fun _ b => finish_ok (fast := fast) hp b))

end
theorem correct {fast : Bool} (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa (VG.Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast) σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of (by dsimp only [r4K] at hs; exact hs)
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h => body_ok (fast := fast) hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by cases fast <;> decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (batch flags fallback finish)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem batch2_ct : RelCT isa (R4 fun σ s => Batch σ 2 0 112 0 s)
    (batch 0 112) (R4 fun σ s => Batch σ 2 0 112 4 s) := by
  refine RelCT.seq (segment_ct (K := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact (segment_ct (K := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))

theorem batch3_ct : RelCT isa (R4 fun σ s => Batch σ 3 112 56 0 s)
    (batch 112 56) (R4 fun σ s => Batch σ 3 112 56 4 s) := by
  refine RelCT.seq (segment_ct (K := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact (segment_ct (K := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))

structure Checked (σ s : State) : Prop where
  prior : ∃ start, Batch σ 2 0 112 4 start ∧ s.mem = start.mem ∧ Keep [.rax, .r14] start s
  r14 : s.gpr .r14 = if allFull σ 280 then 1 else 0
  zf : s.zf = some (!allFull σ 280)

theorem check_ok {σ s : State} (hp : Pre σ) (h : Batch σ 2 0 112 4 s) :
    WP isa (.block (flags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) s (Checked σ) := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  apply WP.block_append
  refine WP.mono (flags_ok hp h.sq.env hj) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  refine ⟨⟨s, h, hm'.trans hm, (hk.trans hk').mono (by simp)⟩, hr'.trans hr, ?_⟩
  rw [hz, hr]; cases allFull σ 280 <;> rfl

theorem check_ct : RelCT isa (R4 fun σ s => Batch σ 2 0 112 4 s)
    (.block (flags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) (R4 Checked) :=
  relInv (fun σ s hp h => check_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem reset_ok {σ s : State} (h : Checked σ s) :
    WP isa (.block [.mov32 .r14 (.imm 1)]) s (Batch σ 2 0 112 4) := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s' ⟨⟨hm, hr⟩, hk⟩ => ?_
  obtain ⟨_, hb, hm₀, hk₀⟩ := h.prior
  exact hb.restore (hm.trans hm₀) ((hk₀.trans hk).mono (by simp)) hr

theorem fallback_ct {fast : Bool} : RelCT isa (R4 Checked) (fallback fast) (R4 Done) := by
  have c : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes 2 1 fast) hc).isSome = true := by
    cases fast <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := c
  refine RelCT.seq (relInv (fun σ s _ h => reset_ok h) (taintRel [] nil_regs (by taint_decide))) ?_
  refine RelCT.seq (relInv (fun σ s hp h => squeeze_last_ok (fast := fast) (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)) ?_
  refine RelCT.seq batch3_ct ?_
  exact relInv (fun σ s hp h => last_flags_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem pub_allFull {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) (n : Nat) :
    allFull σ₁ n = allFull σ₂ n := by
  simp only [allFull, List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and]
  rw [pub_Lt4 hq (K := 0) (by decide), pub_Lt4 hq (K := 1) (by decide),
    pub_Lt4 hq (K := 2) (by decide), pub_Lt4 hq (K := 3) (by decide)]


theorem branch_ct {fast : Bool} : RelCT isa (R4 Checked) (.ite .e (fallback fast) (.block [])) (R4 Done) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.zf = y.zf; rw [h₁.zf, h₂.zf, pub_allFull hq])
    (RelCT.mono (fallback_ct (fast := fast)) (fun _ _ h => h.1) (fun _ _ h => h)) ?_
  have empty : RelCT isa (R4 fun σ s => Checked σ s ∧ allFull σ 280 = true) (.block []) (R4 Done) :=
    relInv (fun σ s _ ⟨h, hf⟩ => by
      obtain ⟨_, hb, hm, hk⟩ := h.prior
      exact WP.block_nil (early_done hb hm hk (by rw [h.r14, hf]; rfl) hf))
      (taintRel [] nil_regs (by taint_decide))
  refine RelCT.mono empty (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_) (fun _ _ h => h)
  have hz : x.zf = some false := hb
  have hf : allFull σ₁ 280 = true := by rw [h₁.zf] at hz; simpa using hz
  exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hf⟩, ⟨h₂, by rw [← pub_allFull hq]; exact hf⟩⟩

theorem finish_ct {fast : Bool} : RelCT isa (R4 fun σ s => Batch σ 2 0 112 4 s) (finish fast) (fun _ _ => True) :=
  RelCT.seq check_ct (RelCT.seq (branch_ct (fast := fast))
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)))

theorem ct {fast : Bool} : ConstantTime isa r4K.pre r4K.pub (VG.Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (start_ct (w16 := false)) (RelCT.seq (RelCT.mono
    (sqT_ct (fast := fast) (t := 0) (by decide) (by decide) (by cases fast <;> exact ⟨_, by taint_decide⟩))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, sqT_of h₁, sqT_of h₂⟩) fun _ _ h => h) ?_))
  refine RelCT.seq (relInv (fun σ s hp h => zeroJ_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide))) ?_
  refine RelCT.seq (segment0_ct (K := 0) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment0_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment0_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment0_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (RelCT.mono (sqM_ct (fast := fast) (by decide) (by decide) (by cases fast <;> exact ⟨_, by taint_decide⟩))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, m2_of h₁, m2_of h₂⟩) fun _ _ h => h) ?_
  exact RelCT.seq (RelCT.mono batch2_ct
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, batch_of_m2 h₁, batch_of_m2 h₂⟩) (fun _ _ h => h)) finish_ct

end VG.Proof.MlDsa.X86_64.Rej4.Segment
