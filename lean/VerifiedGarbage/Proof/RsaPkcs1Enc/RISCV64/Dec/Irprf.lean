module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Prf
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: `CL` and `AM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecIrprf.lean`): the loops of IRPRF's blocks
(`prfLoop_ok`): `CL = IRPRF(KDK, "length", 256)` at `scratch + sCL`
(`clLoop_ok`) and `AM = IRPRF(KDK, "message", k)` at `scratch + sAM`
(`amLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)

/-- After `i` blocks of IRPRF to `scratch + dst` from `t₀`, with the messages `textF`. -/
structure PInv (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (dst : Nat)
    (textF : Nat → List Byte) (t₀ : State) (i : Nat) (t : State) : Prop extends Post s R EM t where
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd
  ctr : t.gpr .s8 = BitVec.ofNat 64 i
  nb : t.gpr .s9 = t₀.gpr .s9
  out : ∀ j < i, Spec.Rsa.bytesAt t.mem (scA s (dst + 32 * j)) 32 = Spec.Hmac.hmac Spec.Hmac.sha256 kd (textF j)
  keep : ∀ a l, sDH ≤ a → a + l ≤ dst → Spec.Rsa.bytesAt t.mem (scA s a) l = Spec.Rsa.bytesAt t₀.mem (scA s a) l

theorem counter_ne {n k : Nat} (hk : k + 1 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1))).toNat ≠ 0 ↔ k + 1 ≠ n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

theorem prfLoop_ok {label : List Nat} {len count : List Instr} {dst N : Nat}
    {kd : List Byte} {C : BitVec 64} {textF : Nat → List Byte} {t₀ : State} (hN0 : 0 < N) (hN : N ≤ 256)
    (hd1 : sCL ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes) (hdst : dst < 2048) (hn : label.length + 4 ≤ 16)
    (htl : ∀ i, (textF i).length = label.length + 4)
    (hC : ∀ i < N, C - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hmsg : ∀ i < N, ∀ u, Post s R EM u → u.gpr .s8 = BitVec.ofNat 64 i →
      WP isa (.block (msgBytes label len)) u fun w =>
        (Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧
          Spec.Rsa.bytesAt w.mem (scA s sMsg) (label.length + 4) = textF i) ∧ Kept [.t1, .t2] u w)
    (hcount : ∀ u : State, u.gpr .s9 = t₀.gpr .s9 →
      WP isa (.block (count ++ [.sub .t1 .t1 .s8])) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C - u.gpr .s8)
    (h0 : PInv s R EM kd dst textF t₀ 0 t₀) :
    WP isa (.loop (prfBody label len dst count) (.nonzero .t1)) t₀ (PInv s R EM kd dst textF t₀ N) := by
  refine VG.Proof.Bignum.RISCV64.count_loop hN0 (PInv s R EM kd dst textF t₀) (fun i hi u hu => ?_) h0
  refine WP.mono (prfBody_ok h hu.toPost hu.kdk hu.ctr (by omega) hd1 (by omega) hdst hn (htl i)
    (hmsg i hi) (fun v hv => hcount v (hv.trans hu.nb))) fun w hw =>
    ⟨⟨hw.toPost, ?_, hw.ctr, hw.nb.trans hu.nb, fun j hj => ?_, fun a l h₁ h₂ => ?_⟩, ?_⟩
  · rw [hw.keep _ _ (by decide) (by unfold scrBytes at hd2; decide) (.inl (by unfold sKDK sCL at *; omega)),
      hu.kdk]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw.keep _ _ (by unfold sDH sCL at *; omega) (by omega) (.inl (by omega)), hu.out j hj]
    · exact hw.out
  · rw [hw.keep _ _ h₁ (by omega) (.inl (by omega)), hu.keep a l h₁ h₂]
  · rw [hw.left, hC i hi]; exact counter_ne hi (by omega)

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

/-! ## The loops -/

theorem count_ok (u : State) {c : Reg} (C : BitVec 64) (hc : u.gpr c = C) :
    WP isa (.block ([mov .t1 c] ++ [.sub .t1 .t1 .s8])) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C - u.gpr .s8 := by
  show WP isa (.block [mov .t1 c, .sub .t1 .t1 .s8]) u _
  exact wp_mov fun v₁ p₁ f₁ => wp_sub fun w p₂ f₂ => wp_nil
    ⟨(p₁.trans p₂).mono, by rw [f₂, f₁, hc, p₁.get .s8]⟩

theorem count8_ok (u : State) :
    WP isa (.block ([.li .t1 8] ++ [.sub .t1 .t1 .s8])) u fun w =>
      Only [.t1] u w ∧ w.gpr .t1 = BitVec.ofNat 64 8 - u.gpr .s8 := by
  show WP isa (.block [.li .t1 (8 : Nat), .sub .t1 .t1 .s8]) u _
  exact wp_li (by decide) fun v₁ p₁ f₁ => wp_sub fun w p₂ f₂ => wp_nil
    ⟨(p₁.trans p₂).mono, by rw [f₂, f₁, p₁.get .s8]⟩

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

/-- A byte of the message buffer is writable. -/
theorem Post.msgW {t : State} (hp : Post s R EM t) :
    ∀ d < 16, InRegions t.wr (scA s sMsg + BitVec.ofNat 64 d) 1 :=
  scByte h hp.wr (a := sMsg) (n := 16) (by decide)

/-- `CL` after its loop. -/
structure CLR (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends Post s R EM t where
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd
  nb : t.gpr .s9 = BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32)
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

theorem clLoop_ok {t : State} {kd : List Byte} (hp : Post s R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd) : WP isa clLoop t (CLR s R EM kd) := by
  have hk := h.k2
  unfold clLoop clInit
  refine WP.seq (wp_li (imm := 0) (by decide) fun v₁ p₁ f₁ => wp_addi (imm := 31) (fun v₂ p₂ f₂ =>
    wp_srl (sh := 5) fun t₁ p₃ f₃ => wp_nil ?_) (by decide))
  have O : Only [.s8, .s9] t t₁ := (p₁.trans (p₂.trans p₃)).mono
  have P₁ : Post s R EM t₁ := hp.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have nb₁ : t₁.gpr .s9 = BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32) := by
    rw [f₃, f₂, p₁.get .s1, hp.s1, nb_eq hk]
  refine WP.mono (prfLoop_ok h (label := lengthLabel) (len := clLen) (count := [.li .t1 8])
    (dst := sCL) (N := 8) (C := BitVec.ofNat 64 8) (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_length, lengthLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi u hu x8 => msgCL_ok (by rw [hu.s0]) x8 (by omega) (hu.msgW h))
    (fun u _ => count8_ok u)
    ⟨P₁, by rw [O.mem, hkd], f₁ ▸ (p₂.get .s8 ▸ p₃.get .s8 ▸ rfl), rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩) fun t₂ h₂ =>
    ⟨h₂.toPost, h₂.kdk, h₂.nb.trans nb₁, ?_⟩
  exact irprf_bytes (N := 8) (by decide) (fun j hj => h₂.out j hj) (by decide)

/-- `AM` after its loop, and `CL` still. -/
structure AMR (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends Post s R EM t where
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256
  am : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .a4).toNat =
    Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .a4).toNat

theorem amLoop_ok {t : State} {kd : List Byte} (hl : CLR s R EM kd t) : WP isa amLoop t (AMR s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold amLoop
  refine WP.seq (wp_li (imm := 0) (by decide) fun t₁ p₁ f₁ => wp_nil ?_)
  have P₁ : Post s R EM t₁ := hl.toPost.keep h p₁.keep (ws := []) (by rw [p₁.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have hN0 : 0 < ((s.gpr .a4).toNat + 31) / 32 := by omega
  refine WP.mono (prfLoop_ok h (label := messageLabel) (len := amLen) (count := [mov .t1 .s9])
    (dst := sAM) (N := ((s.gpr .a4).toNat + 31) / 32) (C := BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32))
    (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++
      Spec.Rsa.i2osp (8 * (s.gpr .a4).toNat) 2)
    hN0 (by omega) (by decide) (by unfold sAM scrBytes; omega) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_message, messageLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi u hu x8 => msgAM_ok (by rw [hu.s0]) x8 hu.s1 (by omega) hk (hu.msgW h))
    (fun u hu => count_ok u _ (by rw [hu, p₁.get .s9, hl.nb]))
    ⟨P₁, by rw [p₁.mem, hl.kdk], f₁, rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.toPost, ?_, ?_⟩
  · rw [h₂.keep _ _ (by decide) (by decide), p₁.mem, hl.cl]
  · exact irprf_bytes rfl (fun j hj => h₂.out j hj) (by omega)

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
