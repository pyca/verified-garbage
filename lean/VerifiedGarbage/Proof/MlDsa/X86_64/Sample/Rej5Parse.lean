module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Parse
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Vec
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt
import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.MlKem.KPke

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
  have e := hI.out (3 * (off + t) + j) hj
  rw [at'] at e
  rw [hI.rsi, at', Offset.add_add, Offset.add_add, e, Xb_getD σ K (by omega)]
  congr 1; omega

theorem hat_regions {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) {s : State} (hI : HAt σ s₀ K h off count t s) {j : Nat}
    (hj : 3 * (off + t) + j < 3 * (off + count)) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [hI.rsi, at', Offset.add_add, Offset.add_add]
  exact in_scr' hp hI.env.rd hI.env.wr (by simp only [oBuf]; omega)

/-- An iteration. -/
theorem hat_step {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (ht : t < count) {s : State}
    (hI : HAt σ s₀ K h off count t s) :
    WP isa rnBody s fun s' => HAt σ s₀ K h off count (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (count - t) - 1 == 0) := by
  refine WP.mono (rnBody_ok s (aP := Proof.MlKem.poly4 (aP σ) K) hI.rbp hI.rdi (Lt_length_le σ K _) (coeffsWr hp hK hI.env)
    hI.stored (by simpa using hat_regions hp hK hspan hI (j := 0) (by omega)) (hat_regions hp hK hspan hI (by omega))
    (hat_regions hp hK hspan hI (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := hat_byte hh hspan hI (j := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  have ht3 : Lt σ K (168 * h + off + (t + 1)) = rnStep (Lt σ K (168 * h + off + t)) ((Xb σ K).getD (3 * (168 * h + off + t)) 0)
      ((Xb σ K).getD (3 * (168 * h + off + t) + 1) 0) ((Xb σ K).getD (3 * (168 * h + off + t) + 2) 0) := by
    simp only [Lt]
    rw [show 3 * (168 * h + off + (t + 1)) = 3 * (168 * h + off + t) + 3 by omega,
      VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [Xb, G_length]; omega),
      rnFold_snoc _ (by rw [List.length_take, Xb, G_length]; omega)]
  rw [e0, hat_byte hh hspan hI (j := 1) (by omega), hat_byte hh hspan hI (j := 2) (by omega), ← ht3] at hdi hst
  have hk' : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := hk
  refine ⟨⟨env_poly hp hK hI.env hf hk'.2.1 hk'.2.2 fun r hr => hk'.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, hI.rsi, Offset.add_add, show 3 * (off + t) + 3 = 3 * (off + (t + 1)) by omega], hdi,
    by rw [hcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
    by rw [hk'.gpr (by decide), hI.rbp],
    fun p hp' => by
      rw [frame_byte hf (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega))
        (Region.contains_self _ _)]
      exact hI.out p hp',
    hst, hI.fr.trans hf, (hI.kp.trans hk').mono (by simp)⟩, by rw [hz, hI.rcx]⟩

/-- A segment of the buffer, from iteration zero. -/
theorem hloop_ok {s₀ : State} {K h off count : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168) (hpos : 0 < count) {s : State} (hI : HAt σ s₀ K h off count 0 s) :
    WP isa (.loop rnBody .ne) s (HAt σ s₀ K h off count count) := by
  refine wp_countdown (N := count) (by omega) (by omega) (fun t u => HAt σ s₀ K h off count t u)
    (fun t ht u hu _ => WP.mono (hat_step hp hK hh hspan ht hu) fun u' ⟨hu', hz⟩ => ⟨hu', ?_, by rw [hz, hu.rcx]⟩)
    (fun _ h => h) hI hI.rcx
  rw [hu'.rcx, hu.rcx, ofNat64_pred (by omega) (by omega)]; rfl


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
  rw [show 3 * (m + 1) = 3 * m + 3 by omega,
    VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [Xb, G_length]; omega),
    rnFold_snoc _ (by rw [List.length_take, Xb, G_length]; omega)]

omit hp in
/-- `k` more iterations, as `stepsG` on the bytes from `3 m`. -/
theorem Lt_steps (σ : State) (K m : Nat) : ∀ k, 3 * (m + k) ≤ 1008 →
    Lt σ K (m + k) = Vec.stepsG (Lt σ K m) (fun p => (Xb σ K).getD (3 * m + p) 0) k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [← Nat.add_assoc, Lt_succ σ K (by omega), Lt_steps σ K m k (by omega), Vec.stepsG]
    simp only [show 3 * (m + k) = 3 * m + 3 * k by omega, Nat.add_assoc]

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
    by rw [k.gpr (by decide), hI.rbp], fun p hp' => by rw [hm]; exact hI.out p (by omega),
    by rw [hm, Nat.add_zero, ← Nat.add_assoc]; exact hI.stored, Frame.refl _ _, ⟨fun _ _ => rfl, rfl, rfl⟩⟩

/-- The end of the scalar loop of a group, with more than 248 coefficients. -/
theorem gb_of_hat {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s s₁ s₂ : State}
    (hI : GB σ s₀ K h off count t s) (hm : s₁.mem = s.mem) (k : Keep [.rcx] s s₁)
    (hA' : HAt σ s₁ K h (off + t) 8 8 s₂) (hl : 248 < (Lt σ K (168 * h + off + t)).length) :
    GB σ s₀ K h off count (t + 8) s₂ ∧ s₂.gpr .r10 = s.gpr .r10 := by
  have hkp : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp, .r10, .r11] s₀ s₂ :=
    ((hI.kp.trans k).trans hA'.kp).mono (by simp)
  refine ⟨⟨hA'.env, by rw [hA'.rsi]; exact congrArg (fun x => at' σ (oBuf + 504 * K) + BitVec.ofNat 64 x) (by omega),
    by rw [hA'.rdi, show 168 * h + (off + t) + 8 = 168 * h + off + (t + 8) by omega], hA'.rbp,
    fun p hp' => by
      rw [frame_byte hA'.fr (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega))
        (Region.contains_self _ _), hm]
      exact hI.out p hp',
    by rw [show 168 * h + off + (t + 8) = 168 * h + (off + t) + 8 by omega]; exact hA'.stored,
    hI.fr.trans (by rw [← hm]; exact hA'.fr), hkp,
    fun h' => absurd h' (by
      have := Lt_mono' σ K (168 * h + off + t) 8 (by omega)
      rw [show 168 * h + off + (t + 8) = 168 * h + off + t + 8 by omega]; omega)⟩,
    by rw [hA'.kp.gpr (by decide), k.gpr (by decide)]⟩

/-- Eight iterations of `vg_mldsa_rej_ntt_poly`'s loop. -/
theorem gsca_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s : State} (hI : GB σ s₀ K h off count t s)
    (hl : 248 < (Lt σ K (168 * h + off + t)).length) :
    WP isa VG.Impl.MlDsa.X86_64.Sample.Rej5.sca8 s fun s' => GB σ s₀ K h off count (t + 8) s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 8)
      (by xrun) rfl) fun s₁ ⟨⟨hm, hc⟩, k⟩ =>
    WP.mono (hloop_ok hp hK hh (by omega) (by decide) (hat0_of ht hI hm k hc)) fun s₂ hA' =>
      gb_of_hat hp hK hh hspan ht hI hm k hA' hl)

/-- The output of eight iterations is in the polynomial. -/
theorem out_reg {K : Nat} (hK : K < 4) {s : State} (he : EnvK σ s) {n : Nat} (hn : n + 4 ≤ 256) :
    InRegions s.wr (Proof.MlKem.poly4 (aP σ) K + BitVec.ofNat 64 (4 * n)) 16 := by
  rw [he.wr, hp.wr]
  exact ⟨aR σ, by simp, by rw [Proof.MlKem.poly4, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩

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
  have hrsi : s.gpr .rsi = at' σ (oBuf + 504 * K + 3 * (off + t)) := by rw [hI.rsi, at', at', Offset.add_add]
  have hbyte : ∀ i < 24, byteY (s.mem.readW (s.gpr .rsi) 256) i = (Xb σ K).getD (3 * (168 * h + off + t) + i) 0 :=
    fun i hi => by
      rw [byteY, byte_readW _ _ (by omega), hrsi, at', Offset.add_add, ← at',
        show oBuf + 504 * K + 3 * (off + t) + i = oBuf + 504 * K + (3 * (off + t) + i) by omega,
        hI.out _ (by omega), Xb_getD σ K (by omega)]
      congr 1; omega
  intro l hl i hi
  simp only [Vec.candK, Vec.candG, gOf]
  rw [hbyte _ (by omega), hbyte _ (by omega), hbyte _ (by omega)]

/-- The candidates of eight iterations and their masks. -/
theorem vec1_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hspan : off + count ≤ 168) (ht : t + 8 ≤ count)
    {s : State} (hI : GB σ s₀ K h off count t s) (hl : (Lt σ K (168 * h + off + t)).length ≤ 248) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.Rej5.vcand) s fun s₁ =>
      VI σ s₀ K h off count t s₁ ∧ s₁.gpr .r10 = s.gpr .r10 := by
  have hrsi : s.gpr .rsi = at' σ (oBuf + 504 * K + 3 * (off + t)) := by rw [hI.rsi, at', at', Offset.add_add]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 32 := by
    rw [hrsi]; exact in_scr' hp hI.env.rd hI.env.wr (by simp only [oBuf]; omega)
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
  have hdi : (s₁.gpr .rdi).toNat = (Lt σ K (168 * h + off + t)).length := by
    rw [g₁ _ (by decide), hI.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbp : s₁.gpr .rbp = Proof.MlKem.poly4 (aP σ) K := by rw [g₁ _ (by decide), hI.rbp]
  have env₁ : EnvK σ s₁ := hI.env.keep m₁ (show Keep [.rax] s s₁ from ⟨fun r hr => g₁ r (by intro e; subst e; simp at hr), rd₁, wr₁⟩)
    (by decide)
  exact WP.mono (Vec.vputA_ok c₁ h0 hax (by rw [g₁ _ (by decide), sy₁]; exact (hI.vec hl).2) (by rw [hdi]; omega)
    (by rw [hbp, hdi]; exact out_reg hp hK env₁ (by omega)))
    fun s₂ hv => ⟨⟨s, s₁, hI, hl, hf, hv⟩, hv.gpr _ (by decide) (by decide) (by decide)⟩

/-- The high lane's coefficients, after `vputA`. -/
theorem vec2b_ok {s₀ : State} {K h off count t : Nat} (hK : K < 4) (hh : h < 2) (hspan : off + count ≤ 168)
    (ht : t + 8 ≤ count) {s₂ : State} (hv : VP σ s₀ K h off count t s₂) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.Rej5.vputB) s₂ fun s' =>
      GB σ s₀ K h off count (t + 8) s' ∧ s'.gpr .r10 = s₂.gpr .r10 := by
  obtain ⟨s, s₁, hI, hl, ⟨hax, h0, c₁, m₁, rd₁, wr₁, sy₁, g₁⟩, hpa⟩ := hv
  have hc := gb_cand hh hspan ht hI
  generalize hX : s.mem.readW (s.gpr .rsi) 256 = X at hax h0 hc hpa
  have hdi : (s₁.gpr .rdi).toNat = (Lt σ K (168 * h + off + t)).length := by
    rw [g₁ _ (by decide), hI.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbp : s₁.gpr .rbp = Proof.MlKem.poly4 (aP σ) K := by rw [g₁ _ (by decide), hI.rbp]
  have e0 := Vec.cntL_eq (hc 0 (by decide))
  have e1 := Vec.cntL_eq (hc 1 (by decide))
  have hA0 : (Vec.accG (gOf σ K h off t) 0).length ≤ 4 := by rw [← e0]; exact Vec.cntL_le X 0
  have hA1 : (Vec.accG (gOf σ K h off t) 1).length ≤ 4 := by rw [← e1]; exact Vec.cntL_le X 1
  have env₁ : EnvK σ s₁ := hI.env.keep m₁ (show Keep [.rax] s s₁ from ⟨fun r hr => g₁ r (by intro e; subst e; simp at hr), rd₁, wr₁⟩)
    (by decide)
  refine WP.mono (Vec.vputB_ok hpa (by rw [g₁ _ (by decide), sy₁]; exact (hI.vec hl).2) (by rw [hdi]; omega)
    (by rw [hbp, hdi]; exact out_reg hp hK env₁ (by have := Vec.cntL_le X 0; omega)))
    fun s₂ ⟨hm₂, hdi₂, hsi₂, c₂, rd₂, wr₂, sy₂, g₂⟩ => ?_
  rw [hbp, hdi, m₁] at hm₂
  rw [hdi, e0, e1] at hdi₂
  have hL8 : Lt σ K (168 * h + off + (t + 8)) = Lt σ K (168 * h + off + t) ++
      Vec.accG (gOf σ K h off t) 0 ++ Vec.accG (gOf σ K h off t) 1 := by
    rw [← Nat.add_assoc, Lt_steps σ K _ 8 (by omega), Vec.stepsG_eight (by simp only [Spec.MlDsa.n]; omega)]
  have st0 := Vec.stored_write4 hI.stored (by omega) hA0 (Vec.compD X 0)
    (fun i hi => Vec.comp_dwords (by decide) (hc 0 (by decide)) i hi)
  have st1 := Vec.stored_write4 st0 (by rw [List.length_append]; omega) hA1 (Vec.compD X 1)
    (fun i hi => Vec.comp_dwords (by decide) (hc 1 (by decide)) i hi)
  rw [List.length_append, ← e0] at st1
  have hf : Frame [pR (Proof.MlKem.poly4 (aP σ) K)] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by have := Vec.cntL_le X 0; omega) (by omega))
  have gk : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₂ r h1 h2 h3 h4, g₁ r h1]
  have k₂ : Keep [.rax, .rdx, .rdi, .rsi] s s₂ := ⟨fun r hr => gk r (by intro e; subst e; simp at hr)
    (by intro e; subst e; simp at hr) (by intro e; subst e; simp at hr) (by intro e; subst e; simp at hr),
    rd₂.trans rd₁, wr₂.trans wr₁⟩
  refine ⟨⟨env_poly hp hK hI.env hf (rd₂.trans rd₁) (wr₂.trans wr₁) (fun r hr => gk r ?_ ?_ ?_ ?_), ?_, ?_,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), hI.rbp],
    fun p hp' => by
      rw [frame_byte hf (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega))
        (Region.contains_self _ _)]
      exact hI.out p hp',
    by rw [hL8, hm₂]; exact st1, hI.fr.trans hf, (hI.kp.trans k₂).mono (by simp),
    fun _ => ⟨c₂, by rw [gk _ (by decide) (by decide) (by decide) (by decide), sy₂, sy₁]; exact (hI.vec hl).2⟩⟩,
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), hpa.gpr _ (by decide) (by decide) (by decide)]⟩
  all_goals try (simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [hsi₂, g₁ _ (by decide), hI.rsi, show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, Offset.add_add]
    exact congrArg (fun x => at' σ (oBuf + 504 * K) + BitVec.ofNat 64 x) (by omega)
  · rw [hL8]
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_append, BitVec.toNat_ofNat]
    rw [hdi₂]
    have := Lt_length_le σ K (168 * h + off + (t + 8))
    rw [hL8] at this
    simp only [List.length_append] at this
    omega


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
  have l₁ : GB σ s₀ K h off count t s₁ := hI.same hg hm hrd hwr sy hl
  have hlen := Lt_length_le σ K (168 * h + off + t)
  rw [hI.rdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hcf
  refine WP.seq (WP.mono (WP.ite _ hcf (fun hb => gvec_ok hp hK hh hspan ht l₁ (by have := of_decide_eq_true hb; omega))
    fun hb => gsca_ok hp hK hh hspan ht l₁ (by have := of_decide_eq_false hb; omega))
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
    in_scr' hp hI.env.rd hI.env.wr (by simp only [oJ]; omega)
  have hsx : BitVec.signExtend 64 (BitVec.ofNat 32 (oBuf + 504 * K + 3 * off)) =
      BitVec.ofNat 64 (oBuf + 504 * K + 3 * off) := sx_ofNat (by simp only [oBuf]; omega)
  have hc : BitVec.setWidth 64 (BitVec.ofNat 32 (count / 8)) = BitVec.ofNat 64 (count / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
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
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ite_eq_left rfl, cst (by decide) (by decide), cst (by decide) (by decide)]; exact c0
    · rw [ite_eq_right (by decide), cst (by decide) (by decide), cst (by decide) (by decide)]; exact c1
  · rw [u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl, u₄.val l hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ite_eq_left rfl, cst (by decide) (by decide), cst (by decide) (by decide)]; exact c2
    · rw [ite_eq_right (by decide), cst (by decide) (by decide), cst (by decide) (by decide)]; exact c3
  · rw [u₆.other _ (by decide) l hl, u₅.val l hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ite_eq_left rfl, cst (by decide) (by decide), cst (by decide) (by decide)]; exact c4
    · rw [ite_eq_right (by decide), cst (by decide) (by decide), cst (by decide) (by decide)]; exact c5
  · rw [u₆.val l hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
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
  refine wp_countdown (cnt := .r10) (N := count / 8) (by omega) (by omega)
    (fun i u => GB σ s K h off count (8 * i) u) (fun i hi u hu _ => ?_) (fun _ h => ?_) (by simpa using h₁) h10
  · exact WP.mono (vgrp_ok hp hK hh hspan (by omega) hu) fun u' ⟨hu', h10', hz⟩ =>
      ⟨by rw [show 8 * i + 8 = 8 * (i + 1) by omega] at hu'; exact hu', h10', hz⟩
  · rwa [show 8 * (count / 8) = count by omega] at h

end
end VG.Proof.MlDsa.X86_64.Rej4.Segment
