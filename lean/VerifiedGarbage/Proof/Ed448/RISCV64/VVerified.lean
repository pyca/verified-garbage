module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.Ed448.RISCV64.VDecode
public import VerifiedGarbage.Proof.Ed448.RISCV64.VJoint
import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeY
import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarBit
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeCheck
import VerifiedGarbage.Proof.Ed448.RISCV64.VSel
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.X448.RISCV64.Mul
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Ed448.RISCV64.VCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Ed448.RISCV64.VMain`, which only this module used -/

section

/-! ### `Ed448.RISCV64.VSetup`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: the setup

`vSetup` rounds the working space up to a multiple of 8 (Ed25519's
`align_ok`, the same two instructions), copies the inputs into it
(`copyB_ok`), points `a0` at `OUT`, clears `BAD`, and writes `d`, `B` and 1
(`vSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Spec.X448 (P Fe)
open VG.Proof.Ed25519.RISCV64 (base)

section
variable {b : Addr}

/-- After `k` bytes of a copy from `src` to `o`. -/
structure CopyInv (b src : Addr) (o : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, k⟩] s0.mem s.mem
  bytes : ∀ i < k, s.mem (b + BitVec.ofNat 64 (o + i)) = s0.mem (src + BitVec.ofNat 64 i)

theorem copyB_ok {s0 : State} (hc : Ctx b s0) {rs : Reg} (hrs : rs ≠ .a4 ∧ rs ≠ .a3) {src : Addr} {so : Nat}
    (h : s0.gpr rs + BitVec.ofNat 64 so = src) {n o : Nat} (hin : ∀ i < n, InRegions (s0.rd ++ s0.wr) (src + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨src, n⟩ ⟨b + BitVec.ofNat 64 o, n⟩) (ho : o + n ≤ 2048) (hso : so + n ≤ 2048) :
    WP isa (.block (copyBytes rs so o n)) s0 (CopyInv b src o s0 n) := by
  obtain ⟨h7, h6⟩ := hrs
  refine wp_range_flatMap (M := isa) (CopyInv b src o s0) (fun k s hk h' => ?_) n (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h'.rest (by decide)
  refine wp_lbz (a := src + BitVec.ofNat 64 k) (by omega_arith)
    (by rw [h'.rest.gpr _ (by simpa using h7), ← h, Offset.add_add])
    (by rw [h'.rest.rd, h'.rest.wr]; exact hin k hk) fun s1 u1 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 (o + k)) (by omega_arith)
    (by rw [u1.other _ (by decide), h'.rest.gpr _ (by decide), hc.a3])
    (by rw [u1.wr, h'.rest.wr]; exact hc.inW (by omega_arith)) fun s2 u2 => WP.block_nil ?_
  have hm2 : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + k)) ((s1.gpr .a4).setWidth 8) := by rw [u2.mem, u1.mem]
  have hsrc : s.mem (src + BitVec.ofNat 64 k) = s0.mem (src + BitVec.ofNat 64 k) :=
    h'.frame _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  refine ⟨h'.rest.trans ((u1.rest (by decide)).trans (u2.rest _)), ?_, fun i hi => ?_⟩
  · rw [hm2]
    exact (h'.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
  · rw [hm2, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [X448.RISCV64.iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))]; exact h'.bytes i hi
    · rw [X448.RISCV64.iteT rfl, u1.gpr, ← hsrc]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := (s.mem (src + BitVec.ofNat 64 i)).isLt
      omega_arith

/-- The bytes of a region apart from a frame's regions stay. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n < 2 ^ 64) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc

theorem bytes_copy {m m0 : Mem} {src : Addr} {o n : Nat}
    (h : ∀ i < n, m (b + BitVec.ofNat 64 (o + i)) = m0 (src + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 o) n = Spec.Ed448.bytesAt m0 src n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [Offset.add_add]; exact h i (List.mem_range.mp hi)

/-- The precondition, by register: `pk` in `a0`, the signature in `a1`, the
challenge in `a2` and `scratch` in `a3`. -/
structure VPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a1, 114⟩, ⟨s.gpr .a2, 57⟩]
  wr : s.wr = [⟨s.gpr .a3, 8192⟩]
  pk_ws : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  sig_ws : (⟨s.gpr .a1, 114⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  ch_ws : (⟨s.gpr .a2, 57⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩

/-- A range of the rounded working space below `8184`, in the working space. -/
theorem base_sub8 (q : Addr) {o n : Nat} (h : o + n ≤ 8184) :
    Region.Sub ⟨base q + BitVec.ofNat 64 o, n⟩ ⟨q, 8192⟩ := by
  have := Align.pad_lt q
  rw [Offset.add_add]
  exact Offset.sub_base _ (by omega_using [h, this])

/-- A range of the rounded working space below `8184`, in the regions of the working space. -/
theorem base_in {rs : List Region} {q : Addr} (hws : (⟨q, 8192⟩ : Region) ∈ rs) {d n : Nat} (h : d + n ≤ 8184) :
    InRegions rs (base q + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt q
  rw [Offset.add_add]
  exact in_base hws (by omega_using [h, this]) (by omega_using [h, this])

/-- The regions the copies write. -/
abbrev copyW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 PK, 57⟩, ⟨b + BitVec.ofNat 64 SG, 57⟩, ⟨b + BitVec.ofNat 64 SGS, 57⟩,
    ⟨b + BitVec.ofNat 64 CH, 57⟩]

/-- The copies of the public key, `R`, `S` and the challenge. -/
theorem copies_ok {s0 : State} (hc : Ctx b s0) {q : Addr}
    (sub8 : ∀ {o n : Nat}, o + n ≤ 8184 → Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ ⟨q, 8192⟩)
    (hrd : s0.rd = [⟨s0.gpr .a0, 57⟩, ⟨s0.gpr .a1, 114⟩, ⟨s0.gpr .a2, 57⟩])
    (pk_ws : (⟨s0.gpr .a0, 57⟩ : Region).Disjoint ⟨q, 8192⟩)
    (sig_ws : (⟨s0.gpr .a1, 114⟩ : Region).Disjoint ⟨q, 8192⟩)
    (ch_ws : (⟨s0.gpr .a2, 57⟩ : Region).Disjoint ⟨q, 8192⟩) :
    WP isa (.block (copyBytes .a0 0 PK 57 ++ copyBytes .a1 0 SG 57 ++ copyBytes .a1 57 SGS 57 ++
        copyBytes .a2 0 CH 57)) s0 fun s4 =>
      Rest [.a4] s0 s4 ∧ Frame (copyW b) s0.mem s4.mem ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s0.mem (s0.gpr .a0) 57 ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 SG) 57 = Spec.Ed448.bytesAt s0.mem (s0.gpr .a1) 57 ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 SGS) 57 =
        Spec.Ed448.bytesAt s0.mem (s0.gpr .a1 + BitVec.ofNat 64 57) 57 ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s0.mem (s0.gpr .a2) 57 := by
  have hPK : PK = 1456 := rfl
  have hSG : SG = 1516 := rfl
  have hSS : SGS = 1576 := rfl
  have hCH : CH = 1636 := rfl
  have hin : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region) ∈ s0.rd → n ≤ 114 → ∀ i < n,
      InRegions (s0.rd ++ s0.wr) (p + BitVec.ofNat 64 i) 1 :=
    fun {p n} hr hn i hi => in_base (P := p) (len := n) (d := i) (n := 1) (List.mem_append_left s0.wr hr)
      (by omega_using [hi]) (by omega_using [hn, hi])
  have sigR : (⟨s0.gpr .a1, 114⟩ : Region) ∈ s0.rd := by rw [hrd]; simp only [List.mem_cons, true_or, or_true]
  have sR : (⟨s0.gpr .a1 + BitVec.ofNat 64 57, 57⟩ : Region).Disjoint ⟨q, 8192⟩ :=
    sig_ws.sub_left (Offset.sub_base (s0.gpr .a1) (d := 57) (n := 57) (k := 114) (by decide))
  have rR : (⟨s0.gpr .a1, 57⟩ : Region).Disjoint ⟨q, 8192⟩ := sig_ws.sub_left (Region.sub_prefix (by omega_arith))
  simp only [List.append_assoc]
  refine WP.append (copyB_ok hc (rs := .a0) (so := 0) (by decide) (BitVec.add_zero _)
    (n := 57) (o := PK) (hin (by rw [hrd]; simp only [List.mem_cons, true_or]) (by omega_arith))
    (pk_ws.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s1 h1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest h1.rest (by decide)
  refine WP.append (copyB_ok hc1 (rs := .a1) (so := 0) (by decide)
    (by rw [h1.rest.gpr _ (by decide), BitVec.add_zero]) (n := 57) (o := SG)
    (by rw [h1.rest.rd, h1.rest.wr]
        exact fun i hi => in_base (List.mem_append_left _ sigR) (by omega_arith) (by omega_arith))
    (rR.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s2 h2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest h2.rest (by decide)
  refine WP.append (copyB_ok hc2 (rs := .a1) (so := 57) (by decide)
    (by rw [h2.rest.gpr _ (by decide), h1.rest.gpr _ (by decide)]) (n := 57) (o := SGS)
    (by rw [h2.rest.rd, h2.rest.wr, h1.rest.rd, h1.rest.wr]
        exact fun i hi => by
          rw [Offset.add_add]
          exact in_base (List.mem_append_left _ sigR) (by omega_arith) (by omega_arith))
    (sR.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s3 h3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest h3.rest (by decide)
  refine WP.mono (copyB_ok hc3 (rs := .a2) (so := 0) (by decide)
    (by rw [h3.rest.gpr _ (by decide), h2.rest.gpr _ (by decide), h1.rest.gpr _ (by decide), BitVec.add_zero])
    (n := 57) (o := CH)
    (by rw [h3.rest.rd, h3.rest.wr, h2.rest.rd, h2.rest.wr, h1.rest.rd, h1.rest.wr]
        exact hin (by rw [hrd]; simp only [List.mem_cons, true_or, or_true]) (by omega_arith))
    (ch_ws.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s4 h4 => ?_
  have dq : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨q, 8192⟩ → ∀ r ∈ copyW b, (⟨p, n⟩ : Region).Disjoint r :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hd.sub_right (sub8 (by omega_arith))
  have k1 : Frame (copyW b) s0.mem s1.mem := h1.frame.mono (by simp)
  have k2 : Frame (copyW b) s1.mem s2.mem := h2.frame.mono (by simp)
  have k3 : Frame (copyW b) s2.mem s3.mem := h3.frame.mono (by simp)
  have k4 : Frame (copyW b) s3.mem s4.mem := h4.frame.mono (by simp)
  have ds : ∀ {o o' : Nat}, o + 57 ≤ o' ∨ o' + 57 ≤ o → o + 57 ≤ 2048 → o' + 57 ≤ 2048 →
      ∀ r ∈ [(⟨b + BitVec.ofNat 64 o', 57⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 o, 57⟩ r :=
    fun h1 h2 h3 r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ h1 (by omega_arith) (by omega_arith)
  refine ⟨h1.rest.trans (h2.rest.trans (h3.rest.trans h4.rest)), k1.trans (k2.trans (k3.trans k4)), ?_, ?_, ?_, ?_⟩
  · rw [bytes_keep h4.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep h3.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep h2.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), bytes_copy h1.bytes]
  · rw [bytes_keep h4.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep h3.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), bytes_copy h2.bytes,
      bytes_keep k1 (dq rR) (by decide)]
  · rw [bytes_keep h4.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), bytes_copy h3.bytes,
      bytes_keep k2 (dq sR) (by decide), bytes_keep k1 (dq sR) (by decide)]
  · rw [bytes_copy h4.bytes, bytes_keep k3 (dq ch_ws) (by decide), bytes_keep k2 (dq ch_ws) (by decide),
      bytes_keep k1 (dq ch_ws) (by decide)]

/-- The regions the constants write. -/
abbrev constW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 DK, 56⟩, ⟨b + BitVec.ofNat 64 ONE, 56⟩]

/-- `a0 = OUT`, `BAD = 0`, and the constants. -/
theorem consts_ok {s4 : State} (hc : Ctx b s4) :
    WP isa (.block (([.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] : List Instr) ++
        constField DK Spec.Ed448.d.val ++ constField ONE 1)) s4 fun t =>
      Rest [.a0, .a4] s4 t ∧ t.gpr .a0 = b + BitVec.ofNat 64 OUT ∧ Frame (constW b) s4.mem t.mem ∧
      bad t.mem b = 0 ∧ FS t.mem b DK = Spec.Ed448.d ∧ FS t.mem b ONE = 1 := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hDK : DK = 336 := rfl
  have hON : ONE = 1400 := rfl
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s5 u5 => wp_addi (by decide) fun s6 u6 => wp_li (by decide) fun s7 u7 => ?_
  have hr7 : Rest [.a0, .a4] s4 s7 := (u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide)))
  have hc7 : Ctx b s7 := hc.of_rest hr7 (by decide)
  refine wp_sd (a := b + BitVec.ofNat 64 BAD) (by decide) (by rw [hc7.a3])
    (al8 hc7.al (by decide)) (hc7.inW (by decide)) fun s8 u8 => ?_
  have hc8 : Ctx b s8 := hc7.of_rest (u8.rest []) (by decide)
  have hm8 : s8.mem = s4.mem.writeW (b + BitVec.ofNat 64 BAD) (BitVec.ofNat 64 0) := by
    rw [u8.mem, u7.gpr, u7.mem, u6.mem, u5.mem]
  refine WP.append (constField_ok hc8 (o := DK) (by decide) (by decide) (fe_lt _)) fun s9 ⟨r9, f9, v9⟩ => ?_
  have hc9 := hc8.of_rest r9 (by decide)
  refine WP.mono (constField_ok hc9 (o := ONE) (by decide) (by decide) (v := 1) (by decide)) fun t ⟨rt, ft, vt⟩ => ?_
  have fB : Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] s4.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (64 / 8))
  refine ⟨hr7.trans ((u8.rest _).trans ((r9.mono (by decide)).trans (rt.mono (by decide)))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [rt.gpr _ (by decide), r9.gpr _ (by decide), u8.gpr, u7.other _ (by decide), u6.gpr, u5.gpr, hc.a3,
      Offset.add_add]
    rfl
  · exact (fB.mono (by simp)).trans ((f9.mono (by simp)).trans (ft.mono (by simp)))
  · have f8t : Frame (constW b |>.drop 1) s8.mem t.mem := (f9.mono (by simp)).trans (ft.mono (by simp))
    unfold bad
    rw [f8t.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        simp only [List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide),
      hm8, Mem.readW_writeW_self64]
    rfl
  · rw [FS, slot_keep ft (by omega_arith) (by omega_arith) (by omega_arith), v9, VG.Proof.X448.toFe_self]
  · rw [FS, vt, VG.Proof.X448.toFe_one]

theorem vSetup_eq : vSetup = Impl.X25519.RISCV64.align ++
    ((copyBytes .a0 0 PK 57 ++ copyBytes .a1 0 SG 57 ++ copyBytes .a1 57 SGS 57 ++ copyBytes .a2 0 CH 57) ++
    (([.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] : List Instr) ++
        constField DK Spec.Ed448.d.val ++ constField ONE 1)) := by
  simp only [vSetup, List.append_assoc]; rfl

theorem vSetup_ok {s : State} (hp : VPre s) :
    WP isa (.block vSetup) s fun t => VCtx (base (s.gpr .a3)) t ∧ Rest [.a0, .a3, .a4] s t ∧
      Frame [⟨s.gpr .a3, 8192⟩] s.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57 ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 SG) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57 ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 SGS) 57 =
        Spec.Ed448.bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 57) 57 ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57 ∧
      bad t.mem (base (s.gpr .a3)) = 0 ∧ FS t.mem (base (s.gpr .a3)) DK = Spec.Ed448.d ∧
      FS t.mem (base (s.gpr .a3)) ONE = 1 := by
  obtain ⟨q, hq⟩ : ∃ q, q = s.gpr .a3 := ⟨_, rfl⟩
  rw [← hq]
  have hws : (⟨q, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hq]; simp
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hPK : PK = 1456 := rfl
  have hSG : SG = 1516 := rfl
  have hSS : SGS = 1576 := rfl
  have hCH : CH = 1636 := rfl
  have hDK : DK = 336 := rfl
  have hON : ONE = 1400 := rfl
  rw [vSetup_eq]
  refine WP.append (Proof.Ed25519.RISCV64.align_ok (q := q) hq.symm hws) fun s0 ⟨hc, h0r, hm0⟩ => ?_
  obtain ⟨b, hb⟩ : ∃ b, b = base q := ⟨_, rfl⟩
  rw [← hb] at hc ⊢
  have sub8 : ∀ {o n : Nat}, o + n ≤ 8184 → Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ ⟨q, 8192⟩ :=
    fun h => by rw [hb]; exact base_sub8 q h
  have g0 : s0.gpr .a0 = s.gpr .a0 := h0r.gpr _ (by decide)
  have g1 : s0.gpr .a1 = s.gpr .a1 := h0r.gpr _ (by decide)
  have g2 : s0.gpr .a2 = s.gpr .a2 := h0r.gpr _ (by decide)
  refine WP.append (copies_ok hc sub8 (by rw [h0r.rd, hp.rd, g0, g1, g2])
    (by rw [g0, hq]; exact hp.pk_ws) (by rw [g1, hq]; exact hp.sig_ws) (by rw [g2, hq]; exact hp.ch_ws))
    fun s4 ⟨r4, f4, ePK, eSG, eSS, eCH⟩ => ?_
  have hc4 : Ctx b s4 := hc.of_rest r4 (by decide)
  refine WP.mono (consts_ok hc4) fun t ⟨rt, at0, ft, bt, dt, ot⟩ => ?_
  rw [hm0, g0] at ePK
  rw [hm0, g1] at eSG eSS
  rw [hm0, g2] at eCH
  have hwt : t.wr = s.wr := by rw [rt.wr, r4.wr, h0r.wr]
  have dc : ∀ {o : Nat}, 1456 ≤ o → o + 57 ≤ 1696 → ∀ r ∈ constW b, Region.Disjoint ⟨b + BitVec.ofNat 64 o, 57⟩ r :=
    fun h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨hc4.of_rest rt (by decide), fun d n hd => by rw [hwt, hb]; exact base_in hws hd, at0⟩,
    (h0r.mono (by decide)).trans ((r4.mono (by decide)).trans (rt.mono (by decide))), ?_,
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), ePK],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eSG],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eSS],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eCH], bt, dt, ot⟩
  have sw : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨q, 8192⟩) → ∀ r ∈ rs, ∃ r' ∈ [(⟨q, 8192⟩ : Region)], Region.Sub r r' :=
    fun h r hr => ⟨_, List.mem_singleton_self _, h r hr⟩
  refine (f4.sub (sw fun r hr => ?_)).trans (ft.sub (sw fun r hr => ?_)) |> fun h => by rw [← hm0]; exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact sub8 (by omega_arith)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub8 (by omega_arith)

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VCheckScalar`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: `S < L`

`checkS` checks that the 57 bytes of `S` (at `SGS`) are below `L`: its
low 448 bits plus `2⁴⁴⁸ - L` do not carry out (scalar reduction's
`subtract_ok`), and its byte 56 is 0 (`checkS_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 ACC)
open VG.Spec.X448 (P Fe)

theorem L_lt448 : Spec.Ed448.L < 256 ^ 56 := by decide +kernel

/-- 57 bytes are below `L` exactly when the last is 0 and the first 56 are. -/
theorem lt_L_iff (bs : List Byte) (h : bs.length = 57) :
    Spec.Ed448.decodeLE bs < Spec.Ed448.L ↔
      (bs.getD 56 0).toNat = 0 ∧ Spec.Ed448.decodeLE (bs.take 56) < Spec.Ed448.L := by
  rw [Proof.Ed448.decodeLE_57 bs h]
  have := L_lt448
  constructor
  · intro hl
    have h0 : (bs.getD 56 0).toNat = 0 := by
      by_contra hne
      have : 256 ^ 56 ≤ 256 ^ 56 * (bs.getD 56 0).toNat := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
      omega_arith
    exact ⟨h0, by omega_using [hl]⟩
  · rintro ⟨h0, h1⟩
    rw [h0, Nat.mul_zero, Nat.add_zero]; exact h1

section
variable {b : Addr}

theorem checkS_ok {s : State} (hc : VCtx b s) :
    WP isa (.block checkS) s fun t => VCtx b t ∧ Rest [.a2, .a4, .a5, .a6] s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem ∧ FS t.mem b DK = FS s.mem b DK ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 (SGS)) 57) < Spec.Ed448.L) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hSS : SGS = 1576 := rfl
  have hSD : SD = 56 := rfl
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  unfold checkS
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (copyIn_ok hc.ctx (p := SGS) (by omega_using [hSS]) (by omega_using [hSS]) (by decide)) fun s1 h1 => ?_
  have hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  refine wp_li (by decide) fun s2 u2 => ?_
  have hc2 : VCtx b s2 := hc1.of_rest (u2.rest (ws := [.a5]) (by decide)) (by decide) (by decide)
  refine WP.append (subtract_ok (o := DY) ⟨by decide, by decide, by decide⟩ hc2.ctx (by rw [u2.gpr]; rfl))
    fun s3 ⟨hr3, hf3, _, h83, _⟩ => ?_
  have hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  refine WP.append (orBad_ok hc3 (r := .a5) (by decide)) fun s4 ⟨hr4, hf4, hb4⟩ => ?_
  have hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_lbz (a := b + BitVec.ofNat 64 (SGS + 56)) (by omega_using [hSS]) (by rw [hc4.ctx.a3])
    (hc4.inR (by omega_using [hSS])) fun s5 u5 => ?_
  have hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.a4]) (by decide)) (by decide) (by decide)
  refine WP.mono (orBad_ok hc5 (r := .a4) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  -- The frames.
  have fC : Frame [FA b] s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  have fS : Frame [FA b] s2.mem s3.mem := hf3.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [hSD])⟩
  have f3 : Frame [FA b] s.mem s3.mem := fC.trans (by rw [u2.mem] at fS; exact fS)
  have hrt' : Rest [.a2, .a4, .a5, .a6] s t := (h1.rest.mono (by decide)).trans
    (((u2.rest (ws := [.a5]) (by decide)).mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr4.mono (by decide)).trans (((u5.rest (ws := [.a4]) (by decide)).mono (by decide)).trans
        (hrt.mono (by decide))))))
  refine ⟨hc.of_rest hrt' (by decide) (by decide), hrt', ?_, ?_, ?_⟩
  · refine (f3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
    rw [← u5.mem]; exact hft.mono (by simp)
  · -- `d` stays.
    have hK : DK = 336 := rfl
    have f : Frame [⟨b + BitVec.ofNat 64 DY, 4 * 14⟩, ⟨b + BitVec.ofNat 64 X2, 4 * 14⟩,
        ⟨b + BitVec.ofNat 64 SD, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem := by
      refine (h1.frame.mono (by simp)).trans ?_
      rw [u2.mem] at hf3
      refine (hf3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
      rw [← u5.mem]; exact hft.mono (by simp)
    have e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [hK, hk]) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- The checks.
    have b3 : bad s3.mem b = bad s.mem b := by
      unfold bad
      rw [f3.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_using [o1, o3]) (by omega_using [o3])) (by decide)]
    have hB : (s5.gpr .a4).toNat = (s.mem (b + BitVec.ofNat 64 (SGS + 56))).toNat := by
      rw [u5.gpr, toNat_imm (Nat.lt_trans (BitVec.isLt _) (by decide)), hf4 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint b (d := SGS + 56) (n := 1) (e := BAD) (k := 8) (by omega_using [o3, hSS])
            (by omega_using [hSS]) (by omega_using [o3]) _ (Region.contains_self _ _) h,
        f3 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint_base b (d := SGS + 56) (n := 1) (k := ACC + 112) (by omega_using [o1, hSS])
            (by omega_using [hSS]) _ (Region.contains_self _ _) h]
    have hV : V s2.mem b DY = yw s.mem b (SGS) := by
      rw [u2.mem]; exact val32_congr fun j hj => (h1.vals j hj).1
    obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem (SGS)
    rw [hbt, u5.mem, hb4, b3, h83, hB, hV, lt_L_iff _ (by simp [Spec.Ed448.bytesAt]), e56, eB,
      Nat.or_eq_zero_iff, Nat.or_eq_zero_iff]
    have : (if Spec.Ed448.L ≤ yw s.mem b (SGS) then 1 else 0) = 0 ↔ yw s.mem b (SGS) < Spec.Ed448.L := by
      by_cases h : Spec.Ed448.L ≤ yw s.mem b (SGS)
      · rw [ite_eq_left h]; exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h (by omega_using [h'])⟩
      · rw [ite_eq_right h]; exact ⟨fun _ => by omega_using [h], fun _ => rfl⟩
    rw [this]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VFinish`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: the result

`vFinish` checks that `Q` is the neutral point, `X = 0` and `Y - Z = 0`
fully reduced, and returns 1 exactly when no check failed (`vFinish_ok`):
1 less the top bit of `BAD | -BAD` (`top_nz`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y Z2 ACC freeze)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

/-- The top bit of `x | -x` is set exactly when `x` is not 0. -/
theorem top_nz (x : BitVec 64) : ((x ||| (0 - x)) >>> 63).toNat = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; decide
  · rw [ite_eq_right h, BitVec.toNat_ushiftRight, BitVec.toNat_or, Nat.shiftRight_or_distrib]
    have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hlt := x.isLt
    have hn : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub]; simp; omega_using [hx]
    rw [hn, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h2 : (2 ^ 64 - x.toNat) / 2 ^ 63 ≤ 1 := by omega_using [hx]
    rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h3 | h3
    · rw [Nat.div_eq_of_lt h3, show (2 ^ 64 - x.toNat) / 2 ^ 63 = 1 by omega_using [hx, h3]]; rfl
    · rw [show x.toNat / 2 ^ 63 = 1 by omega_using [h3]]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with e | e <;> rw [e] <;> rfl

theorem bad_zero_iff {m : Mem} {b : Addr} : (m.readW (b + BitVec.ofNat 64 BAD) 64 = 0) ↔ bad m b = 0 := by
  unfold bad
  exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩

section
variable {b : Addr}

theorem vFinish_ok {s : State} (hc : VCtx b s) {Q : Point} (hS : SlotsOk s.mem b RQ (ptV Q Q)) :
    WP isa (.block vFinish) s fun t =>
      t.gpr .a0 = BitVec.ofNat 64 (if bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z then 1 else 0) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hA := X448.RISCV64.ACC_eq
  have hY : Y = 896 := rfl
  have hdo : Region.Disjoint ⟨b, 2048⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_using [o2]) (by omega_using [o2])).symm
  unfold vFinish
  simp only [outZero, copy, List.append_assoc, List.cons_append]
  -- `X`.
  refine WP.append (freeze_ok hc.ctx hc.a0 (fun k hk => by rw [Offset.add_add]; exact hc.inW (by omega_using [o2, hk])) hdo)
    fun s1 ⟨_, hr1, hf1, hw1⟩ => ?_
  have hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (outOr_ok hc1) fun s2 ⟨hr2, hm2, hv2⟩ => ?_
  have hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  refine WP.append (orBad_ok hc2 (r := .a7) (by decide)) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  have hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  have hS3 := SlotsOk.lo (m := s1.mem) (m' := s3.mem) (by rw [← hm2]; exact hf3) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega_using [o3]) (by omega_using [o3])) (slots_freeze hf1 hdo hS (by decide))
    (by decide)
  -- `Y - Z`.
  refine WP.append (R64.subS (o := TA) (x := RY) (y := RZ) (by decide) (by decide) (by decide) (by decide) hc3.ctx hS3)
    fun s4 ⟨hr4, hf4, hS4⟩ => ?_
  have hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_li (by decide) fun s5 u5 => ?_
  have hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.t0]) (by decide)) (by decide) (by decide)
  have hS5 := hS4
  rw [← u5.mem] at hS5
  refine WP.append (selG (o := X2) (q := TA) (r := TA) (sw := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc5.ctx (by decide) (by rw [u5.gpr]; rfl) hS5 (hS5 TA (by decide)) (hS5 TA (by decide)))
    fun s6 ⟨hr6, hf6, hS6⟩ => ?_
  have hc6 : VCtx b s6 := hc5.of_rest hr6 (by decide) (by decide)
  refine WP.append (freeze_ok hc6.ctx hc6.a0 (fun k hk => by rw [Offset.add_add]; exact hc6.inW (by omega_using [o2, hk])) hdo)
    fun s7 ⟨_, hr7, hf7, hw7⟩ => ?_
  have hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  refine WP.append (outOr_ok hc7) fun s8 ⟨hr8, hm8, hv8⟩ => ?_
  have hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (orBad_ok hc8 (r := .a7) (by decide)) fun s9 ⟨hr9, hf9, hb9⟩ => ?_
  have hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- The result.
  refine wp_ld (a := b + BitVec.ofNat 64 BAD) (by decide) (by rw [hc9.ctx.a3]) (hc9.al8 (by decide))
    (hc9.inR (by omega_using [o3]))
    fun t1 v1 => wp_li (by decide) fun t2 v2 => wp_sub fun t3 v3 => ?_
  refine wp_or fun t4 v4 => wp_srl (by decide) fun t5 v5 => wp_li (by decide) fun t6 v6 => wp_sub fun t7 v7 => ?_
  refine WP.block_nil ?_
  -- `BAD` along the way.
  have rB : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) → bad m' b = bad m b := fun hf hd => by
    unfold bad; rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]
  have dYO : ∀ r ∈ [(⟨b + BitVec.ofNat 64 Y, 56⟩ : Region), ⟨b + BitVec.ofNat 64 OUT, 56⟩],
      Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [o3]) (by omega_arith)
  have dFA : ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_using [o1, o3]) (by omega_using [o3])
  have b1 : bad s1.mem b = bad s.mem b := rB hf1 dYO
  have b8 : bad s8.mem b = bad s3.mem b := by
    rw [bad, hm8, ← bad, rB hf7 dYO, rB hf6 dFA, bad, u5.mem, ← bad, rB hf4 dFA]
  have e9 : bad s9.mem b = bad s.mem b |||
      orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 |||
      orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 := by
    rw [hb9, b8, hb3, hv8, hv2, bad, hm2, ← bad, b1]
  -- The two elements.
  have hX : FS s.mem b X2 = Q.X := by
    rw [hS X2 (by decide)]; simp only [ptV, RX, X2, ↓reduceIte]
  have hYZ : FS s6.mem b X2 = Q.Y - Q.Z := by
    rw [hS6 X2 (by decide)]
    simp only [upd, ptV, pick, VG.Proof.X25519.sel, TA, RX, RY, RZ, X2, Z2, Nat.reduceEqDiff, ↓reduceIte]
  have i1 : orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.X = 0 := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw1, hX]
  have i2 : orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.Y = Q.Z := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw7, hYZ, fin_sub_eq_zero]
  -- The result.
  have ev : t3.gpr .a6 = s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.gpr]
  have e8 : t3.gpr .a5 = 0 - s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.gpr, v2.gpr, v2.other _ (by decide), v1.gpr]; rfl
  have hz : (t5.gpr .a6).toNat = if s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 = 0 then 0 else 1 := by
    rw [v5.gpr, v4.gpr, ev, e8, top_nz]
  rw [v7.gpr, v6.gpr, v6.other _ (by decide)]
  have hc' : (bad s9.mem b = 0) ↔ (bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z) := by
    rw [e9, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, i1, i2, and_assoc]
  apply BitVec.eq_of_toNat_eq
  by_cases h0 : bad s9.mem b = 0
  · rw [ite_eq_left (hc'.mp h0), ite_eq_left (bad_zero_iff.mpr h0)] at *
    rw [BitVec.toNat_sub, hz]; rfl
  · rw [ite_eq_right (fun h => h0 (hc'.mpr h)), ite_eq_right (fun h => h0 (bad_zero_iff.mp h))] at *
    rw [BitVec.toNat_sub, hz]; rfl

end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification equation on RISCV64: the whole function

`vg_ed448_verify_equation` returns 1 exactly when `verifyEquation` holds
(`verifyEquation_correct`), given that `recoverX` is `recoverRef`
(`RecoverOk`, proven in `Proof/Ed448/Facts.lean` and passed in by the
registration): with `-A` and `-R` decoded, `S` checked, the digits of `S`
and `k` recoded and the two tables built, the joint loop leaves `Q`
representing `[S]B + [k](-A)` (`joint_ok`); `[4](Q + (-R))` is the neutral
point exactly when `[4]Q = [4]R`, the equation (`neutral_eq`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC BITS)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)
open VG.Proof.Ed25519.RISCV64 (base)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Impl.Ed448.WnafWide (digitAt residual)

/-! ## The equation -/

theorem pointEqual_identity (q : Point) :
    Spec.Ed448.pointEqual q Spec.Ed448.identity = (decide (q.X = 0) && decide (q.Y = q.Z)) := by
  simp only [Spec.Ed448.pointEqual, Spec.Ed448.identity, Fin.mul_one, Fin.zero_mul, Fin.one_mul]
  rfl

/-- `[4](Q + (-R))` is neutral exactly when the equation holds, for `Q = [S]B + [k](-A)`. -/
theorem neutral_eq {pk sig ch : List Byte} (hl : pk.length = 57) (hs : sig.length = 114) (hc : ch.length = 57)
    {a r : Point} (ha : Spec.Ed448.decodePoint pk = some a) (hr : Spec.Ed448.decodePoint (sig.take 57) = some r)
    {Q : Point} (hQ : Rep Q (Spec.Ed448.decodeLE (sig.drop 57) • baseAff +
      Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a))) :
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual (Proof.Ed448.double (Proof.Ed448.double
          (Spec.Ed448.pointAdd Q (Proof.Ed448.negPoint r)))) Spec.Ed448.identity) := by
  have hR := Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hr)
  rw [Proof.Ed448.verifyEquation_some hl hs hc ha hr hQ hR]
  congr 1
  generalize Spec.Ed448.decodeLE (sig.drop 57) • baseAff + Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a) = x at hQ
  have h1 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hQ)
  have h2 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hR)
  have h3 := Proof.Ed448.double_rep (Proof.Ed448.double_rep (Proof.Ed448.pointAdd_rep hQ hR.neg))
  rw [Bool.eq_iff_iff, Proof.Ed448.pointEqual_rep h1 h2, Proof.Ed448.pointEqual_rep h3 Proof.Ed448.identity_rep,
    Proof.Ed448.four_smul, Proof.Ed448.four_smul, Proof.Ed448.four_smul, smul_add, smul_neg, add_neg_eq_zero]

/-! ## The digits -/

theorem residual_tail {k : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) :
    ∀ n, 464 ≤ n → residual false k n = 0
  | n, h => by
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge n 464 with h' | h'
      · have e : n = 463 := by omega_using [h, h']
        subst e
        exact residual_464 hk
      · show Impl.Ed448.WnafWide.next false (residual false k n) = 0
        rw [ih h']; rfl

theorem digit_tail {k n : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hn : 464 ≤ n) : digitAt false k n = 0 := by
  unfold digitAt; rw [residual_tail hk n hn]; rfl

theorem bit_tail {k i : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hi : 456 ≤ i) :
    Proof.Ed448.WnafWide.bit k i = 0 := by
  unfold Proof.Ed448.WnafWide.bit; rw [Proof.Ed448.WnafWide.tail_quotient hk hi]

/-- The bits written by `bitsOf`. -/
theorem tbSet_bit {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : tbSet 1 K (tbSet 0 S fun _ => 0) h =
      if h % 4 = 0 then Proof.Ed448.WnafWide.bit S (h / 4) else if h % 4 = 1 then Proof.Ed448.WnafWide.bit K (h / 4)
      else 0 := by
  unfold tbSet
  by_cases h0 : h % 4 = 0
  · rw [ite_eq_right (by omega_using [h0]), ite_eq_left h0]
    by_cases hi : h / 4 < 456
    · rw [ite_eq_left ⟨h0, hi⟩, Proof.Ed448.WnafWide.bit_shift]
    · rw [ite_eq_right (fun c => hi c.2), bit_tail hS (by omega_using [hi])]
  · rw [ite_eq_right h0]
    by_cases h1 : h % 4 = 1
    · rw [ite_eq_left h1]
      by_cases hi : h / 4 < 456
      · rw [ite_eq_left ⟨h1, hi⟩, Proof.Ed448.WnafWide.bit_shift]
      · rw [ite_eq_right (fun c => hi c.2), ite_eq_right (by omega_using [h0]), bit_tail hK (by omega_using [hi])]
    · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1]), ite_eq_right (by omega_using [h0])]

theorem dig_eq {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : recCur 1 K (recCur 0 S (tbSet 1 K (tbSet 0 S fun _ => 0)) 464) 464 h = digV S K h := by
  unfold recCur digV
  rw [tbSet_bit hS hK]
  rcases (by omega_using [] : h % 4 = 0 ∨ h % 4 = 1 ∨ h % 4 = 2 ∨ h % 4 = 3) with e | e | e | e <;>
    simp only [e, Nat.reduceEqDiff, false_and, ite_false, ite_true, true_and, Nat.reduceAdd]
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hS (by omega_using [hn])]; rfl
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hK (by omega_using [hn])]; rfl

section
variable {b : Addr}

/-! ## Frames -/

/-- An element whose slot is apart from a frame's regions stays. -/
theorem fs_disj {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {q : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 q, 56⟩ r) :
    FS m' b q = FS m b q := fsD hf hd

theorem disj_decW {d n xo yo : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 1696) (hxo : d + n ≤ xo ∨ xo + 56 ≤ d)
    (hyo : d + n ≤ yo ∨ yo + 56 ≤ d) (hx : xo + 56 ≤ 2048) (hy : yo + 56 ≤ 2048) :
    ∀ r ∈ decW b xo yo, Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hRA : DECODE_RA = 1712 := rfl
  intro r hr
  simp only [decW, yW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  all_goals exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_FAB {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) (h3 : d + n ≤ 1696 ∨ 1704 ≤ d) :
    ∀ r ∈ [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_one {d n e k : Nat} (h1 : d + n ≤ e ∨ e + k ≤ d) (h2 : d + n ≤ 8192) (h3 : e + k ≤ 8192) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 e, k⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ h1 (by omega_using [h2]) (by omega_using [h3])

theorem disj_FA {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) :
    ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)

theorem disj_FAK {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 3976) :
    ∀ r ∈ [FA b, KR b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by unfold KT; omega_using [h2]) (by omega_using [h2]) (by unfold KT; omega_using [])

theorem bytes_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.take_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem bytes_drop (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.drop_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem keyOk_BT {a : VG.Proof.EdwardsLaw.EPoint dZ} {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 BT, 896⟩] m m') (h : KeyOk b a m) : KeyOk b a m' := fun i hi => by
  have hK : KT = 3976 := rfl
  have hB : BT = 5320 := rfl
  rw [kpt_keep hf fun o ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [List.mem_singleton.mp hr]
    rcases ho with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_using [hi, hK, hB]) (by omega_using [hi, hK]) (by omega_using [hB])]
  exact h i hi

theorem limit_of {bs : List Byte} (h : bs.length = 57) :
    Spec.Ed448.decodeLE bs < Impl.Ed448.WnafWide.scalarLimit := by
  have := Proof.Ed448.decodeLE_below h
  unfold Impl.Ed448.WnafWide.scalarLimit Impl.Ed448.WnafWide.pow2
  exact this

theorem bad_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) : bad m' b = bad m b := by
  unfold bad
  rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]

/-- What the code before the joint loop leaves, for the inputs of `s`. -/
def PreOk (s u : State) : Prop :=
  VCtx (base (s.gpr .a3)) u ∧ u.sp = s.sp ∧
    JFix (base (s.gpr .a3)) (Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57))
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57)) u.mem ∧
    FS u.mem (base (s.gpr .a3)) DK = Spec.Ed448.d ∧
    (bad u.mem (base (s.gpr .a3)) = 0 ↔
      (Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57)).isSome ∧
      (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)).isSome ∧
      Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) < Spec.Ed448.L) ∧
    (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57) = some a →
      KeyOk (base (s.gpr .a3)) (-Proof.Ed448.toAffine a) u.mem) ∧
    (∀ r, Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57) = some r →
      FS u.mem (base (s.gpr .a3)) NRX = 0 - r.X ∧ FS u.mem (base (s.gpr .a3)) NRY = r.Y ∧ r.Z = 1)

theorem pre_run (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) : WP isa vPrefix s fun u => PreOk s u ∧
    Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s u := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hTB : TB = 2104 := rfl
  have hKT : KT = 3976 := rfl
  have hBT : BT = 5320 := rfl
  have hSG : SG = 1516 := rfl
  have hSS : SGS = 1576 := rfl
  have hPK : PK = 1456 := rfl
  have hCH : CH = 1636 := rfl
  have hNAX : NAX = 1176 := rfl
  have hNAY : NAY = 1232 := rfl
  have hNRX : NRX = 1288 := rfl
  have hNRY : NRY = 1344 := rfl
  have hONE : ONE = 1400 := rfl
  have hDK : DK = 336 := rfl
  unfold PreOk
  generalize hb : base (s.gpr .a3) = b
  unfold vPrefix
  refine WP.seq (WP.mono (vSetup_ok hp) fun s1 ⟨hc1, hr1, hf1, ePK, eSG, eSS, eCH, hb1, hd1, hone⟩ => ?_)
  rw [hb] at hc1 ePK eSG eSS eCH hb1 hd1 hone
  refine WP.seq (WP.mono (decode_ok hR hc1 (p := SG) (by decide) (by decide) (by decide) (xo := NRX) (yo := NRY)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hd1)
    fun s2 ⟨hc2, hr2, hf2, hd2, hb2, hv2⟩ => ?_)
  refine WP.seq (WP.mono (decode_ok hR hc2 (p := PK) (by decide) (by decide) (by decide) (xo := NAX) (yo := NAY)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hd2)
    fun s3 ⟨hc3, hr3, hf3, hd3, hb3, hv3⟩ => ?_)
  refine WP.seq (WP.mono (checkS_ok hc3) fun s4 ⟨hc4, hr4, hf4, hk4, hb4⟩ => ?_)
  refine WP.seq (WP.mono (bitsZero_ok hc4) fun s5 ⟨hc5, hr5, hf5, ht5⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc5 (src := SGS) (e := 0) (by decide) (by decide) (by decide) ht5)
    fun s6 ⟨hc6, hr6, hf6, ht6⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc6 (src := CH) (e := 1) (by decide) (by decide) (by decide) ht6)
    fun s7 ⟨hc7, hr7, hf7, ht7⟩ => ?_)
  -- What the digits' phases keep: everything below `TB`.
  have dTB : ∀ {d n : Nat}, d + n ≤ 2104 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 TB, 1872⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := fun h => disj_one (.inl (by omega_using [hTB, h])) (by omega_using [h]) (by omega_using [hTB])
  -- The inputs, as the phases read them.
  have kA : Spec.Ed448.bytesAt s2.mem (b + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57 := by
    rw [bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
      (by decide), ePK]
  have kR : Spec.Ed448.bytesAt s1.mem (b + BitVec.ofNat 64 SG) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57 := by rw [eSG, bytes_take]
  have kS3 : Spec.Ed448.bytesAt s3.mem (b + BitVec.ofNat 64 SGS) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57 := by
    rw [bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide), eSS, bytes_drop]
  have kS5 : Spec.Ed448.bytesAt s5.mem (b + BitVec.ofNat 64 SGS) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57 := by
    rw [bytes_keep hf5 (dTB (by omega_using [hSS])) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), kS3]
  have kK : Spec.Ed448.bytesAt s6.mem (b + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57 := by
    rw [bytes_keep hf6 (dTB (by omega_using [hCH])) (by decide), bytes_keep hf5 (dTB (by omega_using [hCH])) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide), eCH]
  rw [kS5] at ht6 ht7
  rw [kK] at ht7
  have hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  have hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  have hKl := limit_of hl5
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) = K at *
  refine WP.seq (WP.mono (recode_ok hc7 (e := 0) (k := S) (by decide) (fun i _ => by
      rw [tbSet_bit hSl hKl, ite_eq_left (by omega_using []), show (4 * i + 0) / 4 = i by omega_using []]) ht7)
    fun s8 ⟨hc8, hr8, hf8, ht8⟩ => ?_)
  refine WP.seq (WP.mono (recode_ok hc8 (e := 1) (k := K) (by decide) (fun i _ => by
      rw [recCur, ite_eq_right (by omega_using []), tbSet_bit hSl hKl, ite_eq_right (by omega_using []), ite_eq_left (by omega_using []),
        show (4 * i + 1) / 4 = i by omega_using []]) ht8)
    fun s9 ⟨hc9, hr9, hf9, ht9⟩ => ?_)
  have hdig : TbIs b s9.mem (digV S K) := fun h hh => by rw [ht9 h hh, dig_eq hSl hKl]
  -- The slots above the field area, from the checks to the digits.
  have k49 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s9.mem b q = FS s4.mem b q := fun h1 h2 => by
    rw [fs_disj hf9 (dTB (by omega_using [h2])), fs_disj hf8 (dTB (by omega_using [h2])), fs_disj hf7 (dTB (by omega_using [h2])),
      fs_disj hf6 (dTB (by omega_using [h2])), fs_disj hf5 (dTB (by omega_using [h2]))]
  have k34 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s4.mem b q = FS s3.mem b q := fun h1 h2 =>
    fs_disj hf4 (disj_FAB (by omega_using [h1]) (by omega_using [h2]) (by omega_using [h2]))
  have kFS1 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1176 ∨ 1400 ≤ q → q + 56 ≤ 1456 → FS s3.mem b q = FS s1.mem b q :=
    fun h1 h2 h3 => by
      rw [fs_disj hf3 (disj_decW (by omega_arith) (by omega_arith) (by unfold NAX; omega_arith)
          (by unfold NAY; omega_arith) (by decide) (by decide)),
        fs_disj hf2 (disj_decW (by omega_arith) (by omega_arith) (by unfold NRX; omega_arith)
          (by unfold NRY; omega_arith) (by decide) (by decide))]
  have kR3 : ∀ {q : Nat}, q = NRX ∨ q = NRY → FS s3.mem b q = FS s2.mem b q := fun h => by
    rcases h with rfl | rfl <;>
      exact fs_disj hf3 (disj_decW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- `-A` and `d` before the tables.
  let A' : Point := ⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩
  have hpA : Pt s9.mem b NAX NAY ONE A' := ⟨rfl, rfl, rfl⟩
  have hd9 : FS s9.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf9 (dTB (by omega_using [hDK])), fs_disj hf8 (dTB (by omega_using [hDK])), fs_disj hf7 (dTB (by omega_using [hDK])),
      fs_disj hf6 (dTB (by omega_using [hDK])), fs_disj hf5 (dTB (by omega_using [hDK])), hk4, hd3]
  refine WP.seq (WP.mono (keyTable_ok hc9 hpA hd9) fun s10 hK10 => ?_)
  have hc10 : VCtx b s10 := hK10.1
  refine WP.mono (baseTable_ok hc10) fun s11 ⟨hc11, hr11, hf11, hB11⟩ => ?_
  have dBT : ∀ {d n : Nat}, d + n ≤ 5320 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 BT, 896⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := fun h => disj_one (.inl (by omega_using [hBT, h])) (by omega_using [h]) (by omega_using [hBT])
  have hfx : JFix b S K s11.mem := ⟨fun h hh => by
      have e1 := hf11 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact fun hc => (dBT (d := TB + h) (n := 1) (by omega_using [hTB, hh]) _ (List.mem_singleton_self _)) _
          (Region.contains_self _ _) hc
      have e2 := hK10.2.2.1 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        exact fun hc => (disj_FAK (d := TB + h) (n := 1) (by omega_using [hTB]) (by omega_using [hTB, hh]) r hr) _ (Region.contains_self _ _) hc
      rw [e1, e2]; exact hdig h hh, hB11⟩
  have hd11 : FS s11.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf11 (dBT (by omega_using [hDK]))]; exact hK10.2.2.2.2.2.2.2.1
  have dF := disj_FA (b := b) (d := BAD) (n := 8) (by omega_using [o3]) (by omega_using [o3])
  have k911 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s11.mem b q = FS s9.mem b q := fun h1 h2 => by
    rw [fs_disj hf11 (dBT (by omega_using [h2])), fs_disj hK10.2.2.1 (disj_FAK (by omega_using [h1]) (by omega_using [h2]))]
  refine ⟨?_, (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans
    ((hr3.mono (by decide)).trans ((hr4.mono (by decide)).trans
    ((hr5.mono (by decide)).trans ((hr6.mono (by decide)).trans
    ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
    ((hr9.mono (by decide)).trans ((hK10.2.1.mono (by decide)).trans (hr11.mono (by decide)))))))))))⟩
  refine ⟨hc11, ?_, hfx, hd11, ?_, fun a hA => ?_, fun r hRr => ?_⟩
  · rw [hr11.sp, hK10.2.1.sp, hr9.sp, hr8.sp, hr7.sp, hr6.sp, hr5.sp, hr4.sp, hr3.sp, hr2.sp, hr1.sp]
  · rw [bad_keep hf11 (dBT (by omega_using [o3])), bad_keep hK10.2.2.1 (disj_FAK (by omega_using [o3]) (by omega_using [o3])),
      bad_keep hf9 (dTB (by omega_using [o3])), bad_keep hf8 (dTB (by omega_using [o3])), bad_keep hf7 (dTB (by omega_using [o3])),
      bad_keep hf6 (dTB (by omega_using [o3])), bad_keep hf5 (dTB (by omega_using [o3])), hb4, hb3, hb2, kA, kR, kS3, hS]
    simp only [hb1, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  · obtain ⟨ax, ay, az⟩ := hv3 a (by rw [kA]; exact hA)
    have eA : A' = Proof.Ed448.negPoint a := by
      show (⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩ : Point) = ⟨0 - a.X, a.Y, a.Z⟩
      rw [k49 (by decide) (by decide), k49 (by decide) (by decide), k49 (by decide) (by decide),
        k34 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide), ax, ay,
        kFS1 (by decide) (by decide) (by decide), hone, az]
    have hArep : Rep A' (-Proof.Ed448.toAffine a) := by
      rw [eA]; exact (Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hA)).neg
    exact keyOk_BT hf11 (keyOk_of hArep hK10)
  · obtain ⟨rx, ry, rz⟩ := hv2 r (by rw [kR]; exact hRr)
    rw [k911 (by decide) (by decide), k911 (by decide) (by decide), k49 (by decide) (by decide),
      k49 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide),
      kR3 (.inl rfl), kR3 (.inr rfl), rx, ry, rz]
    exact ⟨rfl, rfl, rfl⟩

theorem pre_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) : WP isa vPrefix s (PreOk s) :=
  WP.mono (pre_run hR hp) fun _ h => h.1

theorem verifyEquation_correct (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) :
    WP isa verifyEquation s fun t => ((t.gpr .a0).setWidth 32 =
      if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)
        (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) then 1 else 0) ∧
      Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s t := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  have hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  have hKl := limit_of hl5
  unfold verifyEquation
  refine WP.seq (WP.mono (pre_run hR hp) fun u ⟨⟨hcu, _, hfx, hdu, hbad, hkey, hnr⟩, hru⟩ => ?_)
  generalize hb : base (s.gpr .a3) = b at hcu hfx hdu hbad hkey hnr
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) = K at *
  refine WP.seq (WP.mono (joint_ok hSl hKl hcu hfx hdu) fun s12 ⟨sL, hvL, fL, rL, ⟨⟨t2', C12⟩, d12, rep12⟩⟩ => ?_)
  refine WP.seq (WP.mono (addNegR_ok hvL C12 d12) fun s13 ⟨hc13, st13, sl13⟩ => ?_)
  obtain ⟨tf, t, hef, ht, hk⟩ := WP.keep
    [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (vFinish_ok hc13 sl13) (by decide +kernel)
  have rf : Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s13 t :=
    ⟨hk.1, hk.2.1, hk.2.2, Exec.sp hef⟩
  refine ⟨tf, t, hef, ?_, hru.trans ((rL.mono (by decide)).trans
    ((st13.rest.mono (by decide)).trans rf))⟩
  rw [ht]
  have dF := disj_FA (b := b) (d := BAD) (n := 8) (by omega_using [o3]) (by omega_using [o3])
  have hb13 : bad s13.mem b = bad u.mem b := by rw [bad_keep st13.frame dF, bad_keep fL dF]
  have kU : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s12.mem b q = FS u.mem b q := fun h1 h2 => by
    rw [fs_hi C12.stp.frame (by omega_using [o1, h1]) (by omega_using [h2]), fs_hi fL (by omega_using [o1, h1]) (by omega_using [h2])]
  rw [hb13] at *
  have res : ∀ (c : Prop) [Decidable c] (v : Bool), (c ↔ v = true) →
      (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if v then 1 else 0 := by
    intro c _ v h
    by_cases hc : c
    · rw [ite_eq_left hc, ite_eq_left (h.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun hv => hc (h.mpr hv))]; rfl
  refine res _ _ ?_
  cases hA : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57) with
  | none =>
    rw [Proof.Ed448.verifyEquation_none (.inl hA)]
    exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).2.1; rw [hA] at this; exact absurd this (by decide),
      fun h => absurd h (by decide)⟩
  | some a =>
    cases hRr : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57) with
    | none =>
      rw [Proof.Ed448.verifyEquation_none (.inr hRr)]
      exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).1; rw [hRr] at this; exact absurd this (by decide),
        fun h => absurd h (by decide)⟩
    | some r =>
      have hQ := rep12 _ (keyOk_FA fL (hkey a hA))
      simp only [Impl.Ed448.WnafWide.residual, natCast_zsmul] at hQ
      obtain ⟨rx, ry, rz⟩ := hnr r hRr
      have eR : (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = Proof.Ed448.negPoint r := by
        show (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = ⟨0 - r.X, r.Y, r.Z⟩
        rw [kU (by decide) (by decide), kU (by decide) (by decide), rx, ry, rz]
      rw [← hS, ← hK] at hQ
      rw [neutral_eq hl3 hl4 hl5 hA hRr hQ, hS, pointEqual_identity, hbad]
      simp only [hA, hRr, Option.isSome_some, true_and, Bool.and_eq_true, decide_eq_true_eq]
      rw [eR]

end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# `vg_ed448_verify_equation` on RISC-V, verified

The function meets `verifyRISCV64` (`VTiming.lean`), with no stack. Its
correctness proof preserves registers across the shared addition-chain call
and establishes the ABI obligations (`verifyEquation_ok`), and it is
constant time from its pointers and inputs (`verifyEquation_ct`).

Two runs from states with the same pointers and the same inputs leak the same
trace (`verifyEquation_rel`). Everything before the joint loop, its start,
`[4](R + (-R'))` and the end are constant time from the pointers
(`VCT.lean`). In the loop, both runs hold the same digits of the same `S`
and `k` (`pre_ok`, from the same inputs), so at each position both take the
same branches, and each branch is constant time from its digit
(`base_rel`, `key_rel`, `step_rel`, `loop_rel`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.Ed448.RISCV64.Comb (ptOf DQ)
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.RISCV64 (ACC)
open VG.Proof.Ed25519.RISCV64 (base)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Registers and stack pointers equal in two given states. -/
theorem eq2_regs {σ₁ σ₂ : State} {rs : List Reg} (hsp : σ₁.sp = σ₂.sp) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) :
    ∀ a b, Eq2 σ₁ σ₂ a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r := fun a b ⟨ha, hb⟩ => by
  subst ha hb; exact ⟨hsp, hr⟩

section
variable {b : Addr}

/-! ## The digits' branches -/

theorem a5_digit {S K : Nat} {w z l : State} {t2v : BitVec 64} {m : Nat} (hm : m < 464)
    (hc : R64.Cur b w t2v (BitVec.ofNat 64 m) DQ (FS z.mem b) z) (hfx : JFix b S K w.mem) {e : Nat}
    (he : e = 2 ∨ e = 3)
    (h5 : l.gpr .a5 = BitVec.ofNat 64 (z.mem (b + BitVec.ofNat 64 (TB + (4 * m + e)))).toNat) :
    l.gpr .a5 = dByte (digitAt false (if e = 2 then S else K) m) := by
  have hA : ACC = 952 := rfl
  have hT : TB = 2104 := rfl
  rw [h5, byte_hi hc.stp.frame (by omega_using [hA, hT]) (by omega_using [hm, he, hT]), dig_byte hfx.1 (by omega_using [hm]) he]

theorem base_rel {S K : Nat} {w₁ w₂ z₁ z₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {a₁ a₂ : BitVec 64} (c₁ : R64.Cur b w₁ a₁ (BitVec.ofNat 64 m) DQ (FS z₁.mem b) z₁)
    (c₂ : R64.Cur b w₂ a₂ (BitVec.ofNat 64 m) DQ (FS z₂.mem b) z₂) :
    RelCT isa (Eq2 z₁ z₂) addBase TT := by
  have y₁ := vctx_cur hv₁ c₁
  have y₂ := vctx_cur hv₂ c₂
  unfold addBase
  refine rel_seq (load2_ct (eq2_regs (by rw [c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [y₁.a0, y₂.a0]
      · rw [c₁.t1, c₂.t1]))
    (loadDigit_ok y₁ (n := m) (e := 2) (by omega_using [hm]) (by decide) c₁.t1)
    (loadDigit_ok y₂ (n := m) (e := 2) (by omega_using [hm]) (by decide) c₂.t1) fun l₁ l₂ ⟨r₁, _, e₁⟩ ⟨r₂, _, e₂⟩ => ?_
  have d₁ := a5_digit hm c₁ hf₁ (.inl rfl) e₁
  have d₂ := a5_digit hm c₂ hf₂ (.inl rfl) e₂
  refine rel_ite (by rw [eval_nonzero, d₁]) (by rw [eval_nonzero, d₂]) (fun _ => baseBody_ct (eq2_regs
    (by rw [r₁.sp, r₂.sp, c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => ?_))
    (fun _ => (relct_nil (P := Eq2 l₁ l₂)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.a0, y₂.a0]
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.ctx.a3, y₂.ctx.a3]
  · rw [d₁, d₂]

theorem key_rel {S K : Nat} {w₁ w₂ z₁ z₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {a₁ a₂ : BitVec 64} (c₁ : R64.Cur b w₁ a₁ (BitVec.ofNat 64 m) DQ (FS z₁.mem b) z₁)
    (c₂ : R64.Cur b w₂ a₂ (BitVec.ofNat 64 m) DQ (FS z₂.mem b) z₂) :
    RelCT isa (Eq2 z₁ z₂) addKey TT := by
  have y₁ := vctx_cur hv₁ c₁
  have y₂ := vctx_cur hv₂ c₂
  unfold addKey
  refine rel_seq (load3_ct (eq2_regs (by rw [c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [y₁.a0, y₂.a0]
      · rw [c₁.t1, c₂.t1]))
    (loadDigit_ok y₁ (n := m) (e := 3) (by omega_using [hm]) (by decide) c₁.t1)
    (loadDigit_ok y₂ (n := m) (e := 3) (by omega_using [hm]) (by decide) c₂.t1) fun l₁ l₂ ⟨r₁, _, e₁⟩ ⟨r₂, _, e₂⟩ => ?_
  have d₁ := a5_digit hm c₁ hf₁ (.inr rfl) e₁
  have d₂ := a5_digit hm c₂ hf₂ (.inr rfl) e₂
  refine rel_ite (by rw [eval_nonzero, d₁]) (by rw [eval_nonzero, d₂]) (fun _ => keyBody_ct (eq2_regs
    (by rw [r₁.sp, r₂.sp, c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => ?_))
    (fun _ => (relct_nil (P := Eq2 l₁ l₂)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.a0, y₂.a0]
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.ctx.a3, y₂.ctx.a3]
  · rw [d₁, d₂]

/-! ## The loop -/

theorem step_rel {S K : Nat} {w₁ w₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {x₁ x₂ : State} (hx₁ : WInv b S K w₁ (m + 1) x₁) (hx₂ : WInv b S K w₂ (m + 1) x₂) :
    RelCT isa (Eq2 x₁ x₂) jointStep TT := by
  have hx₁' := hx₁
  have hx₂' := hx₂
  obtain ⟨⟨_, cx₁⟩, -, -⟩ := hx₁'
  obtain ⟨⟨_, cx₂⟩, -, -⟩ := hx₂'
  unfold jointStep
  refine rel_seq (dec_ct (eq2_regs (by rw [cx₁.stp.rest.sp, cx₂.stp.rest.sp, hw]) fun r hr => by
      rw [List.mem_singleton.mp hr, cx₁.t1, cx₂.t1]))
    (decStep_ok hm hx₁) (decStep_ok hm hx₂) fun y₁ y₂ ⟨⟨_, cy₁⟩, dy₁, ry₁⟩ ⟨⟨_, cy₂⟩, dy₂, ry₂⟩ => ?_
  refine rel_seq (dbl_ct (eq2_regs (by rw [cy₁.stp.rest.sp, cy₂.stp.rest.sp, hw]) fun r hr => by
      rw [List.mem_singleton.mp hr, cy₁.ctx.a3, cy₂.ctx.a3]))
    (dblStep_ok cy₁ dy₁ ry₁) (dblStep_ok cy₂ dy₂ ry₂) fun z₁ z₂ ⟨⟨_, cz₁⟩, dz₁, rz₁⟩ ⟨⟨_, cz₂⟩, dz₂, rz₂⟩ => ?_
  refine rel_seq (base_rel hv₁ hv₂ hf₁ hf₂ hw hm cz₁ cz₂) (addBase_ok hv₁ hf₁ hm cz₁ dz₁ rz₁)
    (addBase_ok hv₂ hf₂ hm cz₂ dz₂ rz₂) fun q₁ q₂ ⟨⟨_, cq₁⟩, _, _⟩ ⟨⟨_, cq₂⟩, _, _⟩ => ?_
  exact key_rel hv₁ hv₂ hf₁ hf₂ hw hm cq₁ cq₂

theorem loop_rel {S K : Nat} {w₁ w₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp)
    (h₁ : WInv b S K w₁ 464 w₁) (h₂ : WInv b S K w₂ 464 w₂) :
    RelCT isa (Eq2 w₁ w₂) (.loop jointStep (.nonzero .t1)) TT := by
  refine (RelCT.loop (Q := TT) (fun n a b' => 1 ≤ n ∧ n ≤ 464 ∧ WInv b S K w₁ n a ∧ WInv b S K w₂ n b') ?_
    464).mono (fun a b' ⟨ha, hb⟩ => by subst ha hb; exact ⟨by decide, le_refl _, h₁, h₂⟩) fun _ _ h => h
  intro n
  rcases n with _ | m
  · exact RelCT.of_false fun a b' h => absurd h.1 (by decide)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn1, hn2, hs₁, hs₂⟩ e₁ e₂
    have hm : m < 464 := by omega_using [hn2]
    have r := ((step_rel hv₁ hv₂ hf₁ hf₂ hw hm hs₁ hs₂).wp
      (F₁ := fun (t : State) => WInv b S K w₁ m t ∧ (t.gpr .t1 != 0) = decide (m ≠ 0))
      (F₂ := fun (t : State) => WInv b S K w₂ m t ∧ (t.gpr .t1 != 0) = decide (m ≠ 0)) fun a b' ⟨ha, hb⟩ => by
        subst ha hb; exact ⟨jointStep_ok hv₁ hf₁ hm hs₁, jointStep_ok hv₂ hf₂ hm hs₂⟩)
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
    obtain ⟨ht, -, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := r
    refine ⟨ht, ⟨by rw [eval_nonzero, eval_nonzero, z₁, z₂], fun _ => trivial, fun hc => ⟨m, by omega_using [], ?_⟩⟩⟩
    rw [eval_nonzero, z₁] at hc
    have : m ≠ 0 := by simpa using hc
    exact ⟨by omega_using [this], by omega_using [hn2], g₁, g₂⟩

theorem jointLoop_rel {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit)
    (hK : K < Impl.Ed448.WnafWide.scalarLimit) {u₁ u₂ : State} (hv₁ : VCtx b u₁) (hv₂ : VCtx b u₂)
    (hf₁ : JFix b S K u₁.mem) (hf₂ : JFix b S K u₂.mem) (hd₁ : FS u₁.mem b DK = Spec.Ed448.d)
    (hd₂ : FS u₂.mem b DK = Spec.Ed448.d) (hu : u₁.sp = u₂.sp) :
    RelCT isa (Eq2 u₁ u₂) jointLoop TT := by
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  have hDK : DK = 336 := rfl
  unfold jointLoop
  refine rel_seq (init_ct (eq2_regs hu fun r hr => by rw [List.mem_singleton.mp hr, hv₁.ctx.a3, hv₂.ctx.a3]))
    (jointInit_ok hv₁) (jointInit_ok hv₂) fun w₁ w₂ ⟨vw₁, rw₁, fw₁, pw₁, tw₁⟩ ⟨vw₂, rw₂, fw₂, pw₂, tw₂⟩ => ?_
  have fa : ∀ {u w : State}, Frame (R3 b RX RY RZ) u.mem w.mem → Frame [FA b] u.mem w.mem := fun hf =>
    hf.sub fun r hr => ⟨FA b, by simp, by
      have hA : ACC = 952 := rfl
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  have dk : ∀ {u w : State}, Frame (R3 b RX RY RZ) u.mem w.mem → FS w.mem b DK = FS u.mem b DK := fun hf =>
    fsD hf fun r hr => by
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [hDK]) (by omega_arith)
  have start : ∀ {w : State}, VCtx b w → ptOf (FS w.mem b) = Spec.Ed448.identity →
      w.gpr .t1 = BitVec.ofNat 64 464 → FS w.mem b DK = Spec.Ed448.d → WInv b S K w 464 w :=
    fun hv hp ht hd => ⟨⟨_, ⟨hv.ctx, R64.Stp.refl _ _, rfl, ht, fun _ _ => rfl⟩⟩, hd, fun a _ => by
      beta_reduce
      rw [hp, residual_464 hS, residual_464 hK]
      simpa only [Nat.cast_zero, zero_smul, add_zero] using Proof.Ed448.identity_rep⟩
  exact loop_rel vw₁ vw₂ (jfix_FA (fa fw₁) hf₁) (jfix_FA (fa fw₂) hf₂) (by rw [rw₁.sp, rw₂.sp, hu])
    (start vw₁ pw₁ tw₁ (by rw [dk fw₁, hd₁])) (start vw₂ pw₂ tw₂ (by rw [dk fw₂, hd₂]))

end

/-! ## The whole function -/

/-- `verifyEquationContract` by register. -/
def verifyRISCV64 : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 57⟩
    let sig : Region := ⟨s.gpr .a1, 114⟩
    let ch : Region := ⟨s.gpr .a2, 57⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws
  post s s' := (s'.gpr .a0).setWidth 32 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) then 1 else 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a2) 57).map (·.toNat) =
    (Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a2) 57).map (·.toNat)


theorem bytes_parts {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  have hi : Function.Injective (fun x : Byte => x.toNat) := fun x y hxy => BitVec.eq_of_toNat_eq hxy
  have e := List.map_injective_iff.mpr hi h
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verifyEquation_rel (hR : Proof.Ed448.RecoverOk) {σ₁ σ₂ : State} (h₁ : VPre σ₁) (h₂ : VPre σ₂)
    (hpub : verifyRISCV64.pub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) verifyEquation TT := by
  obtain ⟨p0, p1, p2, p3, psp, pb⟩ := hpub
  obtain ⟨-, eS, eK⟩ := bytes_parts (by simp [Spec.Ed448.bytesAt]) (by simp [Spec.Ed448.bytesAt]) pb
  unfold verifyEquation
  refine rel_seq (prefix_ct (eq2_regs psp fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption))
    (pre_ok hR h₁) (pre_ok hR h₂) fun u₁ u₂ ⟨c₁, sp₁, f₁, d₁, _⟩ ⟨c₂, sp₂, f₂, d₂, _⟩ => ?_
  rw [← p3] at c₂ f₂ d₂
  rw [← eS, ← eK] at f₂
  have hl4 : (Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  have hSl := limit_of (bs := (Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  have hKl := limit_of (bs := Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a2) 57) (by simp [Spec.Ed448.bytesAt])
  generalize base (σ₁.gpr .a3) = b at c₁ c₂ f₁ f₂ d₁ d₂
  have hu : u₁.sp = u₂.sp := by rw [sp₁, sp₂, psp]
  refine rel_seq (jointLoop_rel hSl hKl c₁ c₂ f₁ f₂ d₁ d₂ hu) (joint_ok hSl hKl c₁ f₁ d₁) (joint_ok hSl hKl c₂ f₂ d₂)
    fun v₁ v₂ ⟨L₁, vL₁, _, rL₁, ⟨⟨_, cv₁⟩, dv₁, _⟩⟩ ⟨L₂, vL₂, _, rL₂, ⟨⟨_, cv₂⟩, dv₂, _⟩⟩ => ?_
  have hv : v₁.sp = v₂.sp := by rw [cv₁.stp.rest.sp, cv₂.stp.rest.sp, rL₁.sp, rL₂.sp, hu]
  refine rel_seq (addNegR_ct (eq2_regs hv fun r hr => by
      rw [List.mem_singleton.mp hr, cv₁.ctx.a3, cv₂.ctx.a3]))
    (addNegR_ok vL₁ cv₁ dv₁) (addNegR_ok vL₂ cv₂ dv₂) fun t₁ t₂ ⟨ct₁, st₁, _⟩ ⟨ct₂, st₂, _⟩ => ?_
  refine vFinish_ct (eq2_regs (by rw [st₁.rest.sp, st₂.rest.sp, rL₁.sp, rL₂.sp, hu]) fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [ct₁.a0, ct₂.a0]
  · rw [ct₁.ctx.a3, ct₂.ctx.a3]

theorem verifyEquation_ct (hR : Proof.Ed448.RecoverOk) :
    ConstantTime isa verifyRISCV64.pre verifyRISCV64.pub verifyEquation :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (verifyEquation_rel hR (σ₁ := s₁) (σ₂ := s₂) ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2⟩
      ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2⟩ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1


/-! ## Correctness with the ABI -/

open VG VG.RISCV64


open VG VG.RISCV64

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (s : State)
    (hs : verifyRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Ed448.RISCV64.verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, h, hr⟩ := verifyEquation_correct hR ⟨h1, h2, h3, h4, h5⟩
  exact ⟨t, s', he, ⟨fun r hm => hr.gpr r (by cases r <;> simp_all [preserved]),
    hr.sp, hr.gpr .ra (by decide)⟩, h⟩

end VG.Proof.Ed448.RISCV64
