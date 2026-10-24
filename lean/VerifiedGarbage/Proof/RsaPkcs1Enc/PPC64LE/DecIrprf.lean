module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecPrf
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecMsg
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: `CL` and `AM`

The loops of IRPRF's blocks (`prfLoop_ok`): `CL = IRPRF(KDK, "length", 256)`
at `scratch + sCL` (`clLoop_ok`) and `AM = IRPRF(KDK, "message", k)` at
`scratch + sAM` (`amLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

/-- After `i` blocks of IRPRF to `scratch + dst` from `t₀`, with the messages `textF`. -/
structure PInv (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (nbv : BitVec 64) (dst : Nat)
    (textF : Nat → List Byte) (t₀ : State) (i : Nat) (t : State) : Prop where
  post : Post s R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd
  ctr : sl s t oI = BitVec.ofNat 64 i
  nb : sl s t oNB = nbv
  out : ∀ j < i, Spec.Rsa.bytesAt t.mem (scA s (dst + 32 * j)) 32 = Spec.Hmac.hmac Spec.Hmac.sha256 kd (textF j)
  keep : ∀ a l, 1040 ≤ a → a + l ≤ dst → Spec.Rsa.bytesAt t.mem (scA s a) l = Spec.Rsa.bytesAt t₀.mem (scA s a) l

theorem counter_ne {n k : Nat} (hk : k + 1 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1))).toNat ≠ 0 ↔ k + 1 ≠ n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

theorem prfLoop_ok {label : List Nat} {len count : List Instr} {dst N : Nat}
    {kd : List Byte} {nbv C : BitVec 64} {textF : Nat → List Byte} {t₀ : State} (hN0 : 0 < N) (hN : N ≤ 256)
    (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes) (hdst : dst < 2 ^ 15) (hn : label.length + 4 ≤ 16)
    (htl : ∀ i, (textF i).length = label.length + 4)
    (hC : ∀ i < N, C - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hmsg : ∀ i < N, ∀ u, Post s R EM u → u.gpr .r9 = scA s sMsg → u.gpr .r11 = BitVec.ofNat 64 i →
      u.gpr .r8 = s.gpr .r7 → WP isa (.block (msgBytes label len)) u fun w =>
        (Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧
          Spec.Rsa.bytesAt w.mem (scA s sMsg) (label.length + 4) = textF i) ∧ Keep [.r10] u w)
    (hcount : ∀ u, Post s R EM u → sl s u oNB = nbv → WP isa (.block (incr count)) u fun w =>
      (w.mem = u.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s u oI + 1) ∧
        w.gpr .r9 = C - (sl s u oI + 1)) ∧ Keep [.r12, .r11, .r9] u w)
    (h0 : PInv s R EM kd nbv dst textF t₀ 0 t₀) :
    WP isa (.loop (prfBody label len dst count) (.nonzero .d .r9)) t₀ (PInv s R EM kd nbv dst textF t₀ N) := by
  refine VG.Proof.Bignum.PPC64LE.count_loop hN0 (PInv s R EM kd nbv dst textF t₀) (fun i hi u hu => ?_) h0
  refine WP.mono (prfBody_ok h hu.post hu.kdk hu.ctr hu.nb (by omega) hd1 (by omega) hdst hn (htl i)
    (hmsg i hi) hcount) fun w hw => ⟨⟨hw.post, ?_, hw.ctr, hw.nb, fun j hj => ?_, fun a l h₁ h₂ => ?_⟩, ?_⟩
  · rw [hw.keep _ _ (by decide) (by unfold scrBytes at hd2; decide) (.inl (by unfold sKDK; omega)), hu.kdk]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw.keep _ _ (by omega) (by omega) (.inl (by omega)), hu.out j hj]
    · exact hw.out
  · rw [hw.keep _ _ h₁ (by omega) (.inl (by omega)), hu.keep a l h₁ h₂]
  · rw [hw.r9, hC i hi]; exact counter_ne hi (by omega)

end

/-! ## The bytes of the blocks -/

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} (n : Nat) (h : ∀ j < n, f j = g j) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun j hj => h j (by omega)),
      List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.flatMap_nil, h n (by omega)]

theorem bytes_blocks (s : State) (m : Mem) (o : Nat) : ∀ n, Spec.Rsa.bytesAt m (scA s o) (32 * n) =
    (List.range n).flatMap fun j => Spec.Rsa.bytesAt m (scA s (o + 32 * j)) 32
  | 0 => rfl
  | n + 1 => by
    rw [show 32 * (n + 1) = 32 * n + 32 by omega, bytesAt_add, bytes_blocks s m o n, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Offset.add_add]

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem irprf_bytes {s : State} {m : Mem} {kd label : List Byte} {length dst N : Nat} (hN : N = (length + 31) / 32)
    (hout : ∀ j < N, Spec.Rsa.bytesAt m (scA s (dst + 32 * j)) 32 = Proof.RsaPkcs1Enc.prfBlock kd label length j)
    (hl : length ≤ 32 * N) :
    Spec.Rsa.bytesAt m (scA s dst) length = Spec.RsaPkcs1Enc.irprf kd label length := by
  rw [Proof.RsaPkcs1Enc.irprf_eq, ← hN, ← flatMap_range_congr N hout, ← bytes_blocks, ← bytesAt_take _ _ hl]

theorem nb_eq {k : BitVec 64} (hk : k.toNat ≤ 1024) :
    (k + BitVec.ofNat 64 31) >>> 5 = BitVec.ofNat 64 ((k.toNat + 31) / 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## The counters -/

/-- The slots `oI` and `oNB` may be written. -/
theorem slots_safe {s : State} : ∀ r ∈ ([⟨fb s + BitVec.ofNat 64 oI, 8⟩, ⟨fb s + BitVec.ofNat 64 oNB, 8⟩] : List Region),
    Safe s r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr (.inr ⟨oI, Nat.le_refl _, show oI + 8 ≤ oLr by decide, rfl⟩)
  · exact .inr (.inr ⟨oNB, by decide, show oNB + 8 ≤ oLr by decide, rfl⟩)


section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

/-- A byte of the message buffer is writable. -/
theorem Post.msgW {t : State} (hc : Post s R EM t) :
    ∀ d < 16, InRegions t.wr (scA s sMsg + BitVec.ofNat 64 d) 1 := fun d hd => by
  rw [Offset.add_add]
  exact scIn h hc.wr (a := sMsg + d) (n := 1) (by unfold sMsg scrBytes; omega)

/-- A write of the slots leaves `scratch` as it was. -/
theorem slots_scr {m m' : Mem}
    (hf : Frame [⟨fb s + BitVec.ofNat 64 oI, 8⟩, ⟨fb s + BitVec.ofNat 64 oNB, 8⟩] m m') {a l : Nat}
    (ha : a + l ≤ scrBytes) : Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l :=
  bytes_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact (((h.ks.sub_left (frame_sub s (by decide))).sub_right (sc_sub h)).sub_right (scSub ha)).symm)
    (by unfold scrBytes at ha; omega)

/-- After `clInit`: the counter zero, the number of `AM`'s blocks in its slot, and `scratch` as before. -/
theorem clStart_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block clInit) t fun t₁ => Post s R EM t₁ ∧ sl s t₁ oI = BitVec.ofNat 64 0 ∧
      sl s t₁ oNB = BitVec.ofNat 64 (((s.gpr .r7).toNat + 31) / 32) ∧ ∀ a l, a + l ≤ scrBytes →
        Spec.Rsa.bytesAt t₁.mem (scA s a) l = Spec.Rsa.bytesAt t.mem (scA s a) l := by
  have hk := h.k2
  have c1 : oI < 2 ^ 15 ∧ oI % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c3 : oNB < 2 ^ 15 ∧ oNB % 4 = 0 := by decide
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  have o1 := slotOut (u := t) hc.wr (d := oI) (by decide) (by decide)
  have o3 := slotOut (u := t) hc.wr (d := oNB) (by decide) (by decide)
  have rk : (t.mem.writeW (fb s + BitVec.ofNat 64 oI) (BitVec.ofNat 64 0)).readW (fb s + BitVec.ofNat 64 oK) 64 =
      s.gpr .r7 := by
    rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]; exact hc.sl.k
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r10] (Q := fun u =>
    u.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 oI) (BitVec.ofNat 64 0)).writeW (fb s + BitVec.ofNat 64 oNB)
      ((s.gpr .r7 + BitVec.ofNat 64 31) >>> 5)) ?_ rfl) fun t₁ ⟨m₁, k₁⟩ => ?_
  · unfold clInit
    prun [fp, exec_addSp0, hc.sp, c1, c2, c3, i2, o1, o3, rk,
      exec_addi (show Reg.r10 ≠ .r0 by decide) (show 31 < 2 ^ 15 by decide)]
  have F₁ : Frame [⟨fb s + BitVec.ofNat 64 oI, 8⟩, ⟨fb s + BitVec.ofNat 64 oNB, 8⟩] t.mem t₁.mem := by
    rw [m₁]
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_cons_self ..) _ ?_)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_ <;> exact Region.contains_self _ _
  refine ⟨hc.step h k₁.rd k₁.wr k₁.sp (fun r hr => k₁.gpr r (by revert r; decide)) F₁ (slots_safe (s := s)),
    ?_, ?_, fun a l ha => slots_scr h F₁ ha⟩
  · show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_self64, nb_eq hk]

/-- After `AM`'s counter is zeroed: `scratch` as before. -/
theorem amStart_ok {t : State} (hc : Post s R EM t)
    (hnb : sl s t oNB = BitVec.ofNat 64 (((s.gpr .r7).toNat + 31) / 32)) :
    WP isa (.block [fp, .li .r10 0, .store .d .r10 .r12 oI]) t fun t₁ =>
      Post s R EM t₁ ∧ sl s t₁ oI = BitVec.ofNat 64 0 ∧
      sl s t₁ oNB = BitVec.ofNat 64 (((s.gpr .r7).toNat + 31) / 32) ∧ ∀ a l, a + l ≤ scrBytes →
        Spec.Rsa.bytesAt t₁.mem (scA s a) l = Spec.Rsa.bytesAt t.mem (scA s a) l := by
  have c1 : oI < 2 ^ 15 ∧ oI % 4 = 0 := by decide
  have o1 := slotOut (u := t) hc.wr (d := oI) (by decide) (by decide)
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r10] (Q := fun u =>
    u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oI) (BitVec.ofNat 64 0)) ?_ rfl) fun t₁ ⟨m₁, k₁⟩ => ?_
  · prun [fp, exec_addSp0, hc.sp, c1, o1]
  have F₁ : Frame [⟨fb s + BitVec.ofNat 64 oI, 8⟩, ⟨fb s + BitVec.ofNat 64 oNB, 8⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)
  refine ⟨hc.step h k₁.rd k₁.wr k₁.sp (fun r hr => k₁.gpr r (by revert r; decide)) F₁ (slots_safe (s := s)),
    ?_, ?_, fun a l ha => slots_scr h F₁ ha⟩
  · show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_self64]
  · show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hnb

/-! ## The loops -/

/-- `CL` after its loop. -/
structure CLR (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  post : Post s R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd
  nb : sl s t oNB = BitVec.ofNat 64 (((s.gpr .r7).toNat + 31) / 32)
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

theorem clLoop_ok {t : State} {kd : List Byte} (hc : Post s R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd) : WP isa clLoop t (CLR s R EM kd) := by
  refine WP.seq (WP.mono (clStart_ok h hc) fun t₁ ⟨hc₁, ct₁, nb₁, kp₁⟩ => ?_)
  refine WP.mono (prfLoop_ok h (label := lengthLabel) (len := clLen) (count := [.li .r9 8])
    (dst := sCL) (N := 8) (C := BitVec.ofNat 64 8) (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_length, lengthLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi u hu x9 x11 _ => msgCL_ok x9 x11 (by omega) (hu.msgW h))
    (fun u hu _ => incrCL_ok hu)
    ⟨hc₁, by rw [kp₁ _ _ (by decide), hkd], ct₁, nb₁, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.post, h₂.kdk, h₂.nb, ?_⟩
  exact irprf_bytes (N := 8) (by decide) (fun j hj => h₂.out j hj) (by decide)

/-- `AM` after its loop, and `CL` still. -/
structure AMR (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  post : Post s R EM t
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256
  am : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .r7).toNat =
    Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .r7).toNat

theorem amLoop_ok {t : State} {kd : List Byte} (hl : CLR s R EM kd t) : WP isa amLoop t (AMR s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  refine WP.seq (WP.mono (amStart_ok h hl.post hl.nb) fun t₁ ⟨hc₁, ct₁, nb₁, kp₁⟩ => ?_)
  have hN0 : 0 < ((s.gpr .r7).toNat + 31) / 32 := by omega
  refine WP.mono (prfLoop_ok h (label := messageLabel) (len := amLen) (count := [.load .d .r9 .r12 oNB])
    (dst := sAM) (N := ((s.gpr .r7).toNat + 31) / 32) (C := BitVec.ofNat 64 (((s.gpr .r7).toNat + 31) / 32))
    (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++
      Spec.Rsa.i2osp (8 * (s.gpr .r7).toNat) 2)
    hN0 (by omega) (by decide) (by unfold sAM scrBytes; omega) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_message, messageLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi u hu x9 x11 x8 => msgAM_ok x9 x11 x8 (by omega) hk (hu.msgW h))
    (fun u hu hnb' => WP.mono (incrAM_ok hu) fun w ⟨⟨a, b⟩, c⟩ => ⟨⟨a, by rw [b, hnb']⟩, c⟩)
    ⟨hc₁, by rw [kp₁ _ _ (by decide), hl.kdk], ct₁, nb₁, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.post, ?_, ?_⟩
  · rw [h₂.keep _ _ (by decide) (by decide), kp₁ _ _ (by decide), hl.cl]
  · exact irprf_bytes rfl (fun j hj => h₂.out j hj) (by omega)

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
