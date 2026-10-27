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
  exact Offset.sub_base _ (by omega)

/-- A range of the rounded working space below `8184`, in the regions of the working space. -/
theorem base_in {rs : List Region} {q : Addr} (hws : (⟨q, 8192⟩ : Region) ∈ rs) {d n : Nat} (h : d + n ≤ 8184) :
    InRegions rs (base q + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt q
  rw [Offset.add_add]
  exact in_base hws (by omega) (by omega)

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
      (by omega) (by omega)
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
  [⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 DK, 56⟩, ⟨b + BitVec.ofNat 64 BX, 56⟩,
    ⟨b + BitVec.ofNat 64 BY, 56⟩, ⟨b + BitVec.ofNat 64 ONE, 56⟩]

/-- `a0 = OUT`, `BAD = 0`, and the constants. -/
theorem consts_ok {s4 : State} (hc : Ctx b s4) :
    WP isa (.block (([.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] : List Instr) ++
        constField DK Spec.Ed448.d.val ++ constField BX Spec.Ed448.basePoint.X.val ++
        constField BY Spec.Ed448.basePoint.Y.val ++ constField ONE 1)) s4 fun t =>
      Rest [.a0, .a4] s4 t ∧ t.gpr .a0 = b + BitVec.ofNat 64 OUT ∧ Frame (constW b) s4.mem t.mem ∧
      bad t.mem b = 0 ∧ FS t.mem b DK = Spec.Ed448.d ∧ FS t.mem b BX = Spec.Ed448.basePoint.X ∧
      FS t.mem b BY = Spec.Ed448.basePoint.Y ∧ FS t.mem b ONE = 1 := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hDK : DK = 336 := rfl
  have hBX : BX = 1064 := rfl
  have hBY : BY = 1120 := rfl
  have hON : ONE = 1400 := rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append]
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
  refine WP.append (constField_ok hc9 (o := BX) (by decide) (by decide) (fe_lt _)) fun s10 ⟨r10, f10, v10⟩ => ?_
  have hc10 := hc9.of_rest r10 (by decide)
  refine WP.append (constField_ok hc10 (o := BY) (by decide) (by decide) (fe_lt _)) fun s11 ⟨r11, f11, v11⟩ => ?_
  have hc11 := hc10.of_rest r11 (by decide)
  refine WP.mono (constField_ok hc11 (o := ONE) (by decide) (by decide) (v := 1) (by decide)) fun t ⟨rt, ft, vt⟩ => ?_
  have fB : Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] s4.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (64 / 8))
  refine ⟨hr7.trans ((u8.rest _).trans ((r9.mono (by decide)).trans ((r10.mono (by decide)).trans
      ((r11.mono (by decide)).trans (rt.mono (by decide)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rt.gpr _ (by decide), r11.gpr _ (by decide), r10.gpr _ (by decide), r9.gpr _ (by decide), u8.gpr,
      u7.other _ (by decide), u6.gpr, u5.gpr, hc.a3, Offset.add_add]
    rfl
  · exact (fB.mono (by simp)).trans ((f9.mono (by simp)).trans ((f10.mono (by simp)).trans
      ((f11.mono (by simp)).trans (ft.mono (by simp)))))
  · have f8t : Frame (constW b |>.drop 1) s8.mem t.mem :=
      (f9.mono (by simp)).trans ((f10.mono (by simp)).trans ((f11.mono (by simp)).trans (ft.mono (by simp))))
    unfold bad
    rw [f8t.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        simp only [List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide),
      hm8, Mem.readW_writeW_self64]
    rfl
  · rw [FS, slot_keep ft (by omega_arith) (by omega_arith) (by omega_arith),
      slot_keep f11 (by omega_arith) (by omega_arith) (by omega_arith),
      slot_keep f10 (by omega_arith) (by omega_arith) (by omega_arith), v9, VG.Proof.X448.toFe_self]
  · rw [FS, slot_keep ft (by omega_arith) (by omega_arith) (by omega_arith),
      slot_keep f11 (by omega_arith) (by omega_arith) (by omega_arith), v10, VG.Proof.X448.toFe_self]
  · rw [FS, slot_keep ft (by omega_arith) (by omega_arith) (by omega_arith), v11, VG.Proof.X448.toFe_self]
  · rw [FS, vt, VG.Proof.X448.toFe_one]

theorem vSetup_eq : vSetup = Impl.X25519.RISCV64.align ++
    ((copyBytes .a0 0 PK 57 ++ copyBytes .a1 0 SG 57 ++ copyBytes .a1 57 SGS 57 ++ copyBytes .a2 0 CH 57) ++
    (([.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] : List Instr) ++
        constField DK Spec.Ed448.d.val ++ constField BX Spec.Ed448.basePoint.X.val ++
        constField BY Spec.Ed448.basePoint.Y.val ++ constField ONE 1)) := by
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
      FS t.mem (base (s.gpr .a3)) BX = Spec.Ed448.basePoint.X ∧
      FS t.mem (base (s.gpr .a3)) BY = Spec.Ed448.basePoint.Y ∧
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
  have hBX : BX = 1064 := rfl
  have hBY : BY = 1120 := rfl
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
  refine WP.mono (consts_ok hc4) fun t ⟨rt, at0, ft, bt, dt, xt, yt, ot⟩ => ?_
  rw [hm0, g0] at ePK
  rw [hm0, g1] at eSG eSS
  rw [hm0, g2] at eCH
  have hwt : t.wr = s.wr := by rw [rt.wr, r4.wr, h0r.wr]
  have dc : ∀ {o : Nat}, 1456 ≤ o → o + 57 ≤ 1696 → ∀ r ∈ constW b, Region.Disjoint ⟨b + BitVec.ofNat 64 o, 57⟩ r :=
    fun h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨hc4.of_rest rt (by decide), fun d n hd => by rw [hwt, hb]; exact base_in hws hd, at0⟩,
    (h0r.mono (by decide)).trans ((r4.mono (by decide)).trans (rt.mono (by decide))), ?_,
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), ePK],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eSG],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eSS],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eCH], bt, dt, xt, yt, ot⟩
  have sw : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨q, 8192⟩) → ∀ r ∈ rs, ∃ r' ∈ [(⟨q, 8192⟩ : Region)], Region.Sub r r' :=
    fun h r hr => ⟨_, List.mem_singleton_self _, h r hr⟩
  refine (f4.sub (sw fun r hr => ?_)).trans (ft.sub (sw fun r hr => ?_)) |> fun h => by rw [← hm0]; exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact sub8 (by omega_arith)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact sub8 (by omega_arith)

end

end VG.Proof.Ed448.RISCV64
