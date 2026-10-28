module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Pointer
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearTop
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearFinish
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearValues
import VerifiedGarbage.Proof.RsaKeyGen.NearWords32
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Whether `|c − p|` in array 2 is at most the threshold, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.RsaKeyGen.X86.Near (bit)
local notation "nword" => VG.Proof.RsaKeyGen.X86.Near.word

theorem orLoop_ok {t₀ : State} {W : Addr} {L x N : Nat} (hw : Ws t₀ W L) (positive : 0 < N)
    (fit : x + 4 * N ≤ L) (P : PtrAt t₀ W .ebp x) (count : (t₀.gpr .ecx).toNat = N) (zero : t₀.gpr .ebx = 0#32) :
    WP isa (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne) t₀
      fun u => (u.gpr .ebx = 0#32 ↔ val32 t₀.mem W x N = 0) ∧ u.mem = t₀.mem ∧
        PtrAt u W .ebp (x + 4 * N) ∧ Keeps [.ebx, .ebp, .ecx] t₀ u := by
  have nowrap := hw.nowrap
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop positive (fun j t =>
      Keeps [.ebx, .ebp, .ecx] t₀ t ∧ t.mem = t₀.mem ∧ PtrAt t W .ebp (x + 4 * j) ∧
      (t.gpr .ecx).toNat = N - j ∧ (t.gpr .ebx = 0#32 ↔ val32 t₀.mem W x j = 0)) ?_
    ⟨Keeps.refl _ _, rfl, by simpa using P, by simpa using count, by rw [zero]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩)
    fun u ⟨K, M, Pu, _, Z⟩ => ⟨Z, M, Pu, K⟩
  rintro j t index ⟨K, M, Pt, cnt, Z⟩
  have ht := hw.of_keeps K
  refine wp_orS (readSrc_ptr ht Pt (d := 0) (by omega)) fun a A => wp_addS rfl fun b B _ =>
    wp_subZ rfl fun u U Zf => WP.block_nil ?_
  obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf cnt index
  have ecxB : b.gpr .ecx = t.gpr .ecx := by rw [B.other .ecx (by decide), A.other .ecx (by decide)]
  refine ⟨⟨K.trans (((A.keeps.mono (by decide)).widen B.keeps).widen U.keeps), ?_, ?_, by rw [U.gpr, ecxB]; exact next, ?_⟩,
    by rw [Zf, ecxB, last]⟩
  · rw [U.mem, B.mem, A.mem, M]
  · rw [PtrAt, U.other .ebp (by decide), B.gpr, A.other .ebp (by decide)]
    exact VG.Proof.Bignum.X86.PublicRt.ptr4 Pt
  · rw [U.other .ebx (by decide), B.other .ebx (by decide), A.gpr, BitVec.or_eq_zero_iff, Z, M, Nat.add_zero]
    have wordZero : t₀.mem.readW (off W (x + 4 * j)) 32 = 0#32 ↔ w32 t₀.mem W (x + 4 * j) = 0 :=
      ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩
    rw [wordZero, val32_succ]
    have power : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    constructor
    · rintro ⟨left, right⟩
      rw [left, right, Nat.mul_zero]
    · intro sum
      have product : 2 ^ (32 * j) * w32 t₀.mem W (x + 4 * j) = 0 := by omega
      exact ⟨by omega, (Nat.mul_eq_zero.mp product).resolve_left (Nat.ne_of_gt power)⟩

theorem orScanSetup_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa (.block (([.mov .ebx (.imm 0)] : List Instr) ++ lenPtr .ebp .edx 2 ++
      ([.mov .ecx (.mem (sc 4)), .shift .shr .ecx 2, .alu .sub .ecx (.imm 4)] : List Instr))) s fun u =>
      PtrAt u W .ebp (slot w 2) ∧ (u.gpr .ecx).toNat = 2 * w - 4 ∧ u.gpr .ebx = 0#32 ∧ u.mem = s.mem ∧
        Keeps [.ebx, .ebp, .ecx, .edx] s u := by
  have width := S.width
  have bound := S.widthBound
  refine WP.block_append (WP.block_append (wp_movS rfl fun a A _ => WP.block_nil ?_))
  have Sa := S.keepMem A.keeps (by decide) (by decide) A.mem
  refine WP.mono (lenPtr_ok Sa 2 (by decide) (by decide : Reg.edx ≠ .ebp) (by decide) (by decide))
    fun b ⟨P, Mb, Kb⟩ => ?_
  have Sb := Sa.keepMem Kb (by decide) (by decide) Mb
  refine wp_movS Sb.lenRead fun c C _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun d D =>
    wp_subS rfl fun u U _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, by rw [U.mem, D.mem, C.mem, Mb, A.mem],
    ((((A.keeps.mono (by decide)).trans (Kb.mono (by decide))).widen C.keeps).widen D.keeps).widen U.keeps⟩
  · rw [PtrAt, U.other .ebp (by decide), D.other .ebp (by decide), C.other .ebp (by decide)]; exact P
  · rw [U.gpr, D.gpr, C.gpr, BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  · rw [U.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide), Kb.1 .ebx (by decide), A.gpr]
    rfl

theorem orScan_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa orScan s fun t =>
      (t.gpr .ebx = 0#32 ↔ val32 s.mem W (slot w 2) (2 * w - 4) = 0) ∧ t.mem = s.mem ∧
        PtrAt t W .ebp (slot w 2 + 4 * (2 * w - 4)) ∧ Keeps [.ebx, .ebp, .ecx, .edx] s t := by
  have width := S.width
  have space := S.space
  have fit : slot w 2 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega
  unfold orScan
  refine WP.seq (WP.mono (orScanSetup_ok S) fun u ⟨Pu, cnt, zero, Mu, Ku⟩ => ?_)
  refine WP.mono (orLoop_ok (S.ws.of_keeps Ku) (by omega) (by omega) Pu cnt zero) fun t ⟨Z, M, Pt, Kt⟩ => ?_
  rw [Mu] at Z
  exact ⟨Z, M.trans Mu, Pt, Ku.trans (Kt.mono (by decide))⟩

theorem topAt_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x) (fit : x + 16 ≤ L) :
    WP isa (.block top) s fun t =>
      t.gpr .ecx = nword s.mem W x >>> 28 ∧
      t.gpr .ebx = s.gpr .ebx ||| (nword s.mem W x &&& 0x0fffffff) ∧
      t.gpr .edx = (nword s.mem W (x + 4) ||| nword s.mem W (x + 8)) ||| nword s.mem W (x + 12) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold top
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega)) fun a A _ => wp_movS rfl fun b B _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun c C => wp_andi fun d D => wp_orS rfl fun e E => ?_
  have Ke : Keeps [.eax, .ebx, .ecx] s e :=
    ((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps
  have Me : e.mem = s.mem := E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))
  have Pe : PtrAt e W .ebp x := by rw [PtrAt, Ke.1 .ebp (by decide)]; exact P
  have he := hw.of_keeps Ke
  refine wp_movS (readSrc_ptr he Pe (d := 4) (by omega)) fun f F _ => ?_
  have Pf : PtrAt f W .ebp x := by rw [PtrAt, F.other .ebp (by decide)]; exact Pe
  refine wp_orS (readSrc_ptr (he.of_keeps F.keeps) Pf (d := 8) (by omega)) fun h H => ?_
  have Ph : PtrAt h W .ebp x := by rw [PtrAt, H.other .ebp (by decide)]; exact Pf
  refine wp_orS (readSrc_ptr ((he.of_keeps F.keeps).of_keeps H.keeps) Ph (d := 12) (by omega)) fun t T =>
    WP.block_nil ?_
  refine ⟨?_, ?_, ?_, T.mem.trans (H.mem.trans (F.mem.trans Me)),
    (((Ke.mono (by decide)).widen F.keeps).widen H.keeps).widen T.keeps⟩
  · rw [T.other .ecx (by decide), H.other .ecx (by decide), F.other .ecx (by decide),
      E.other .ecx (by decide), D.other .ecx (by decide), C.gpr, B.gpr, A.gpr, Nat.add_zero]
    rfl
  · rw [T.other .ebx (by decide), H.other .ebx (by decide), F.other .ebx (by decide), E.gpr,
      D.other .ebx (by decide), C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide),
      D.gpr, C.other .eax (by decide), B.other .eax (by decide), A.gpr, Nat.add_zero]
    rfl
  · rw [T.gpr, H.gpr, F.gpr, H.mem, F.mem, Me]
    rfl

theorem near_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    WP isa near s fun t =>
      t.gpr .eax = bit (decide (val32 s.mem W (slot w 2) (2 * w) ≤ 2 ^ (32 * (2 * w) - 100))) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have width := S.width
  have space := S.space
  have fit : slot w 2 + 4 * (2 * w) ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega
  unfold near
  refine WP.seq (WP.mono (orScan_ok S) fun a ⟨Z, Ma, Pa, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (topAt_ok (S.ws.of_keeps Ka) Pa (by omega)) fun b ⟨C, Lo, H, Mb, Kb⟩ => ?_)
  rw [Ma] at C Lo H
  have bound : (b.gpr .ecx).toNat < 16 := by rw [C]; exact Near.nibble_bound _
  have nibble : (b.gpr .ecx).toNat = w32 s.mem W (slot w 2 + 4 * (2 * w - 4)) / 2 ^ 28 := by
    rw [C, Near.nibble_value]
    rfl
  have low : (b.gpr .ebx).toNat = 0 ↔ val32 s.mem W (slot w 2) (2 * w - 4) = 0 ∧
      w32 s.mem W (slot w 2 + 4 * (2 * w - 4)) % 2 ^ 28 = 0 := by
    rw [Lo, Near.low_zero, Z]
    rfl
  have high : (b.gpr .edx).toNat = 0 ↔ val32 s.mem W (slot w 2 + 4 * (2 * w - 4) + 4) 3 = 0 := by
    rw [← Near.word_zero, H]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using Near.high_zero s.mem W (slot w 2 + 4 * (2 * w - 4) + 4)
  refine WP.mono (Near.finish_ok b bound) fun t ⟨value, Mt, Kt⟩ => ?_
  refine ⟨?_, Mt.trans (Mb.trans Ma), ((Ka.mono (by decide)).widen Kb).widen Kt⟩
  rw [value, nibble]
  have lowFlag : decide ((b.gpr .ebx).toNat ≠ 0) =
      decide (val32 s.mem W (slot w 2) (2 * w - 4) ≠ 0 ∨ w32 s.mem W (slot w 2 + 4 * (2 * w - 4)) % 2 ^ 28 ≠ 0) :=
    decide_eq_decide.mpr (by omega)
  rw [lowFlag, decide_eq_decide.mpr high, Bool.and_comm, ← Bool.decide_and]
  apply congrArg bit
  exact decide_eq_decide.mpr (VG.Proof.RsaKeyGen.near_words32 s.mem W (slot w 2) (2 * w) (by omega)).symm

end VG.Proof.RsaKeyGen.X86.FrontRt
