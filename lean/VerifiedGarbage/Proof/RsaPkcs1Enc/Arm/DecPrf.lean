module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecMem
public import VerifiedGarbage.Proof.Sha1.Arm.Lit
public import VerifiedGarbage.Proof.Sha256.Arm.Lit
public import VerifiedGarbage.Proof.Sha512.Arm.Lit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecFns
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecD
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry

/-! ### `RsaPkcs1Enc.Arm.DecMsg`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the message of an IRPRF block

`I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)` (`msgV`), written byte by byte in
order to `scratch + sMsg` (`MW`, `msgBytes_wp`): the two bytes of `i`, the
label's (`putLabel`), and the bit length's (`clLen` for 256 bytes, `amLen`
for `k`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_strb op2_imm op2_reg op2_lsl op2_lsr dpVal)

variable {P : EP}

/-- The message's place. -/
abbrev msgA (P : EP) : Addr := (sc P sMsg 16).base

/-- The message of block `i`, for the label `lab` and `length` bytes. -/
def msgV (i : Nat) (lab : List Byte) (L : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ lab ++ Spec.Rsa.i2osp (8 * L) 2

theorem msgV_length (i : Nat) (lab : List Byte) (L : Nat) : (msgV i lab L).length = lab.length + 4 := by
  simp [msgV, VG.Proof.RsaPkcs1Enc.i2osp_length]; omega_arith

/-- The message's first `n` bytes written, memory changed only in its 16
bytes and the registers but `r2` kept. -/
structure MW (P : EP) (σ s₀ : State) (xs : List Byte) (n : Nat) (t : State) : Prop where
  st : S P σ t
  frame : Frame [sc P sMsg 16] s₀.mem t.mem
  regs : ∀ r, r ≠ .r2 → t.gpr r = s₀.gpr r
  bytes : ∀ j < n, t.mem (msgA P + BitVec.ofNat 64 j) = xs.getD j 0

section
variable {σ s₀ t : State} {xs : List Byte} {n : Nat}

theorem MW.start (hs : S P σ s₀) : MW P σ s₀ xs 0 s₀ :=
  ⟨hs, Frame.refl _ _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem MW.upd (h : MW P σ s₀ xs n t) {t' : State} {v : BitVec 32} (u : Upd t t' .r2 v) : MW P σ s₀ xs n t' :=
  ⟨⟨h.st.1, h.st.2.of_rest (u.rest (ws := [.r2]) (by simp)) u.mem⟩, by rw [u.mem]; exact h.frame,
    fun r hr => by rw [u.other r hr]; exact h.regs r hr, fun j hj => by rw [u.mem]; exact h.bytes j hj⟩

/-- `strb rt, [r0, #n]` of byte `n`. -/
theorem MW.strb (h : MW P σ s₀ xs n t) (hr0 : s₀.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {rt : Reg} (hb : (t.gpr rt).setWidth 8 = xs.getD n 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → t'.gpr = t.gpr → WP isa (.block is) t' Q) :
    WP isa (.block (.strb rt .r0 n :: is)) t Q := by
  have hs := h.st
  have ha : State.addr (t.gpr .r0 + BitVec.ofNat 32 n) = msgA P + BitVec.ofNat 64 n := by
    rw [h.regs _ (by decide), hr0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sMsg]; omega_arith)]
    exact (Offset.add_ofNat_add_ofNat _ _ _).symm
  refine wp_strb (by omega_arith) ha (by rw [Offset.add_ofNat_add_ofNat]; exact St.sc_w hs (by simp only [sMsg]; omega_arith))
    fun t' u => k t' ⟨⟨hs.1, ?_⟩, ?_, fun r hr => by rw [u.gpr]; exact h.regs r hr, ?_⟩ u.gpr
  · refine hs.2.write (rs := [sc P sMsg 16]) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hs.1.sc_sub (by decide)⟩) u.rd u.wr u.sp
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · intro j hj
    rw [u.mem, WriteBytes.writeW8_apply]
    by_cases e : j = n
    · subst e; simp [hb]
    · simp only [Offset.add_ofNat_ne (msgA P) (by omega_arith) (by omega_arith) e, ↓reduceIte]
      exact h.bytes j (by omega_arith)

theorem setWidth_ofNat8 (v : Nat) : (BitVec.ofNat 32 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- `putByte n v`: the byte `v` at index `n`. -/
theorem MW.putByte (h : MW P σ s₀ xs n t) (hr0 : s₀.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {v : Nat} (hv : v < 256) (hb : xs.getD n 0 = BitVec.ofNat 8 v) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → WP isa (.block is) t' Q) :
    WP isa (.block (putByte n v ++ is)) t Q :=
  wp_mov (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith))) fun t1 u1 =>
    (h.upd u1).strb hr0 hn (by rw [u1.gpr, setWidth_ofNat8, hb]) fun t2 h2 _ => k t2 h2

/-- `putLabel vs n`: the bytes `vs` from index `n`. -/
theorem MW.putLabel (hr0 : s₀.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) :
    ∀ (vs : List Nat) {n : Nat} {t : State}, MW P σ s₀ xs n t → n + vs.length ≤ 16 → (∀ v ∈ vs, v < 256) →
      (∀ j < vs.length, xs.getD (n + j) 0 = BitVec.ofNat 8 (vs.getD j 0)) →
      ∀ {is : List Instr} {Q : State → Prop}, (∀ t', MW P σ s₀ xs (n + vs.length) t' → WP isa (.block is) t' Q) →
      WP isa (.block (Impl.RsaPkcs1Enc.Arm.Decrypt.putLabel vs n ++ is)) t Q
  | [], n, t, h, _, _, _, _, _, k => by simpa [Impl.RsaPkcs1Enc.Arm.Decrypt.putLabel] using k t h
  | v :: vs, n, t, h, hn, hv, hb, _, _, k => by
    simp only [Impl.RsaPkcs1Enc.Arm.Decrypt.putLabel, List.append_assoc]
    refine h.putByte hr0 (by simp at hn; omega_arith) (hv v (by simp)) (by simpa using hb 0 (by simp)) fun t1 h1 => ?_
    refine MW.putLabel hr0 vs h1 (by simp at hn; omega_arith) (fun w hw => hv w (by simp [hw]))
      (fun j hj => by rw [show n + 1 + j = n + (j + 1) by omega_arith, hb (j + 1) (by simp; omega_arith)]; rfl)
      fun t2 h2 => k t2 (by simpa [Nat.add_assoc, Nat.add_comm 1] using h2)

end

/-! ## The whole message -/

theorem i2osp_two_lt {i : Nat} (hi : i < 256) : Spec.Rsa.i2osp i 2 = [0, BitVec.ofNat 8 i] := by
  rw [VG.Proof.RsaPkcs1Enc.i2osp_two, Nat.div_eq_of_lt hi]; rfl

/-- The message: its bytes, from the label's bytes `vs` and the code `len`
of the bit length's two bytes. -/
theorem msgBytes_wp {σ s : State} {vs : List Nat} {len : List Instr} {L i : Nat} (hs : S P σ s)
    (hr0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (hr1 : s.gpr .r1 = BitVec.ofNat 32 i) (hi : i < 256)
    (hvs : vs.length + 4 ≤ 16) (hv : ∀ v ∈ vs, v < 256)
    (hlen : ∀ {t : State}, MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
      ∀ {Q : State → Prop}, (∀ t', MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 4) t' → Q t') →
      WP isa (.block len) t Q) :
    WP isa (.block (msgBytes vs len)) s fun t =>
      S P σ t ∧ Frame [sc P sMsg 16] s.mem t.mem ∧ (∀ r, r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Spec.Rsa.bytesAt t.mem (sc P sMsg (vs.length + 4)).base (vs.length + 4) = msgV i (vs.map (BitVec.ofNat 8)) L := by
  have hm : (msgV i (vs.map (BitVec.ofNat 8)) L).length = vs.length + 4 := by rw [msgV_length]; simp
  unfold msgBytes
  refine (MW.start (xs := msgV i (vs.map (BitVec.ofNat 8)) L) hs).putByte hr0 (by decide) (v := 0) (by decide)
    (by simp only [msgV, i2osp_two_lt hi]; rfl) fun t1 h1 => ?_
  refine h1.strb hr0 (by decide) (by rw [h1.regs _ (by decide), hr1, setWidth_ofNat8]; simp [msgV, i2osp_two_lt hi])
    fun t2 h2 _ => ?_
  refine MW.putLabel hr0 vs h2 (by omega_arith) hv (fun j hj => ?_) fun t3 h3 => ?_
  · simp only [msgV, i2osp_two_lt hi, List.cons_append, List.nil_append]
    rw [show 0 + 1 + 1 + j = j + 2 by omega_arith, List.getD_cons_succ, List.getD_cons_succ,
      getD_append_left _ _ _ (by simp; omega_arith)]
    simp [List.getD_eq_getElem?_getD, hj]
  · refine hlen (by simpa [Nat.add_comm] using h3) fun t4 h4 => ⟨h4.st, h4.frame, h4.regs, ?_⟩
    rw [← hm]
    exact bytesAt_eq fun j hj => by rw [hm] at hj; exact h4.bytes j hj

/-- The bit length 2048 (`clLen`), after a label of 6 bytes. -/
theorem clLen_wp {σ s t : State} {lab : List Byte} {i : Nat} (hl : lab.length = 6)
    (hr0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (h : MW P σ s (msgV i lab 256) 8 t) {Q : State → Prop}
    (k : ∀ t', MW P σ s (msgV i lab 256) 10 t' → Q t') : WP isa (.block clLen) t Q := by
  have e8 : (msgV i lab 256).getD 8 0 = BitVec.ofNat 8 0x08 := by
    simp only [msgV]
    rw [getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have e9 : (msgV i lab 256).getD 9 0 = BitVec.ofNat 8 0x00 := by
    simp only [msgV]
    rw [getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have := h.putByte hr0 (by decide) (v := 0x08) (by decide) e8 (is := putByte 9 0) fun t1 h1 =>
    h1.putByte hr0 (by decide) (v := 0) (by decide) e9 (is := []) fun t2 h2 => WP.block_nil (k t2 h2)
  simpa [clLen, putByte] using this

theorem shl3 (K : Nat) : BitVec.ofNat 32 K <<< 3 = BitVec.ofNat 32 (8 * K) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem shr8 {K : Nat} (hK : K ≤ 1024) : BitVec.ofNat 32 (8 * K) >>> 8 = BitVec.ofNat 32 (8 * K / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- The bit length `8 k` (`amLen`), after a label of 7 bytes, from `k` in `r3`. -/
theorem amLen_wp {σ s t : State} {lab : List Byte} {i K : Nat} (hl : lab.length = 7) (hK : K ≤ 1024)
    (hr0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (hr3 : s.gpr .r3 = BitVec.ofNat 32 K)
    (h : MW P σ s (msgV i lab K) 9 t) {Q : State → Prop}
    (k : ∀ t', MW P σ s (msgV i lab K) 11 t' → Q t') : WP isa (.block amLen) t Q := by
  have r3 : t.gpr .r3 = BitVec.ofNat 32 K := by rw [h.regs _ (by decide), hr3]
  have e9 : (msgV i lab K).getD 9 0 = BitVec.ofNat 8 (8 * K / 256) := by
    simp only [msgV]
    rw [getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have e10 : (msgV i lab K).getD 10 0 = BitVec.ofNat 8 (8 * K) := by
    simp only [msgV]
    rw [getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  refine wp_mov (op2_lsl (by decide)) fun t1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t2 u2 => ?_
  refine ((h.upd u1).upd u2).strb hr0 (by decide) (rt := .r2)
    (by rw [u2.gpr, u1.gpr, r3, shl3, shr8 hK, setWidth_ofNat8, e9]) fun t3 h3 g3 => ?_
  have r3' : t3.gpr .r3 = BitVec.ofNat 32 K := by rw [g3, u2.other _ (by decide), u1.other _ (by decide), r3]
  refine wp_mov (op2_lsl (by decide)) fun t4 u4 => ?_
  refine (h3.upd u4).strb hr0 (by decide) (rt := .r2)
    (by rw [u4.gpr, r3', shl3, setWidth_ofNat8, e10]) fun t5 h5 _ => WP.block_nil (k t5 h5)

end VG.Proof.RsaPkcs1Enc.Arm.Dec

end

end

/-! ### `RsaPkcs1Enc.Arm.DecKdk`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.DecHash`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.HashCalls`, which only this module used -/

section

/-!
# The ARMv7 PKCS #1 v1.5 functions: their callees SHA-256 and HMAC-SHA-256

The contracts of SHA-256's `init`, `update` and `finalize` and of
HMAC-SHA-256's `init` (for a key of any length) and `finalize` (with their
working space in their own frames), at a call with given arguments: what the call needs (`*_pre`), that
two calls with the same arguments are related as their contract asks
(`*_pub`), and what the call gives (`*_post`). The 64-bit `count` is in
`r2:r3`, the low word in `r2`; ours are below `2^32`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm

open VG VG.Arm VG.Proof.RsaPkcs1Sig.Arm

/-- The `S` bytes below a call's stack pointer. -/
abbrev lowR (sp : BitVec 32) (S : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 S, S⟩

theorem count_eq {lo : Nat} (h : lo < 2 ^ 32) :
    (0 : BitVec 32) ++ BitVec.ofNat 32 lo = BitVec.ofNat 64 lo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega_using [h])]
  simp

/-! ## SHA-256's `init(state)` -/

theorem shInit_pre {s : State} {st : BitVec 32} (h0 : s.gpr .r0 = st) (fit : st.toNat + 96 ≤ 2 ^ 32) :
    (Spec.Sha256.initContract abi).pre (s.callEntry.withRegions [] [⟨State.addr st, 96⟩]) := by
  sig_pre [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argRegs, reduceClassify, Loc.val]
  rw [h0]
  exact ⟨by have := s.sp.isLt; omega_using [], rfl, fit⟩

theorem shInit_pub {s₁ s₂ : State} {st : BitVec 32} (h₁ : s₁.gpr .r0 = st) (h₂ : s₂.gpr .r0 = st)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Sha256.initContract abi).pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argRegs, reduceClassify, Loc.val]
  exact ⟨hsp, by rw [h₁, h₂]⟩

theorem shInit_post {s t : State} {st : BitVec 32} (h0 : s.gpr .r0 = st) {rd wr : List Region}
    (hp : (Spec.Sha256.initContract abi).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr)) :
    Spec.Sha256.Repr t.mem (State.addr st) [] := by
  sig_post [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argRegs, reduceClassify, Loc.val] at hp
  rw [h0] at hp
  exact hp

/-! ## SHA-256's `update(state, count, data, len)` -/

/-- The call's arguments. -/
structure UpdArgs (s : State) (st data : BitVec 32) (len cnt : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r2 : s.gpr .r2 = BitVec.ofNat 32 cnt
  r3 : s.gpr .r3 = 0
  a0 : stackArg s 0 = data
  a1 : stackArg s 1 = BitVec.ofNat 32 len
  len32 : len < 2 ^ 32
  cnt32 : cnt < 2 ^ 32

abbrev updRd (sp data : BitVec 32) (len : Nat) : List Region := [⟨State.addr data, len⟩, ⟨State.addr sp, 8⟩]
abbrev updWr (st : BitVec 32) : List Region := [⟨State.addr st, 96⟩]

section
variable {s : State} {st data : BitVec 32} {len cnt : Nat}

theorem upd_pre {sp : BitVec 32} (h : UpdArgs s st data len cnt) (hspE : s.sp = sp) (hsp : 624 ≤ sp.toNat)
    (hsa : sp.toNat + 8 ≤ 2 ^ 32) (dSD : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr data, len⟩)
    (dSA : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr sp, 8⟩)
    (lo : ∀ r ∈ updWr st ++ updRd sp data len, (lowR sp 624).Disjoint r)
    (fS : st.toNat + 96 ≤ 2 ^ 32) (fD : data.toNat + len ≤ 2 ^ 32) :
    (Spec.Sha256.updateContract abi 624).pre (s.callEntry.withRegions (updRd sp data len) (updWr st)) := by
  subst hspE
  sig_pre [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.a0, h.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.len32]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  exact ⟨hsp, hsa, rfl, rfl, dSD, dSA, lo _ (by simp [State.addr]), lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), fS, fD⟩

theorem upd_pub {s₁ s₂ : State} (h₁ : UpdArgs s₁ st data len cnt) (h₂ : UpdArgs s₂ st data len cnt)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Sha256.updateContract abi 624).pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r2, h₁.r3, h₁.a0, h₁.a1, h₂.r0, h₂.r2, h₂.r3, h₂.a0, h₂.a1]
  exact ⟨hsp, trivial, trivial, trivial, trivial, trivial⟩

theorem upd_post {t : State} (h : UpdArgs s st data len cnt) {rd wr : List Region}
    (hp : (Spec.Sha256.updateContract abi 624).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr))
    {iv : Spec.Sha256.HashValue} {msg : List Byte} (hr : Spec.Sha256.ReprFrom iv s.mem (State.addr st) msg)
    (hl : msg.length = cnt) :
    Spec.Sha256.ReprFrom iv t.mem (State.addr st) (msg ++ Spec.Rsa.bytesAt s.mem (State.addr data) len) := by
  sig_post [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost, abi, argRegs,
    reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r2, h.r3, h.a0, h.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.len32] at hp
  exact hp iv msg hr (by rw [count_eq h.cnt32, hl])

end

/-! ## SHA-256's `finalize(state, count, out)` -/

/-- The call's arguments. -/
structure FinArgs (s : State) (st out : BitVec 32) (cnt : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r2 : s.gpr .r2 = BitVec.ofNat 32 cnt
  r3 : s.gpr .r3 = 0
  a0 : stackArg s 0 = out
  cnt32 : cnt < 2 ^ 32

abbrev finRd (sp : BitVec 32) : List Region := [⟨State.addr sp, 4⟩]
abbrev finWr (st out : BitVec 32) : List Region := [⟨State.addr st, 96⟩, ⟨State.addr out, 32⟩]

section
variable {s : State} {st out : BitVec 32} {cnt : Nat}

theorem fin_pre {sp : BitVec 32} (h : FinArgs s st out cnt) (hspE : s.sp = sp) (hsp : 624 ≤ sp.toNat)
    (hsa : sp.toNat + 4 ≤ 2 ^ 32) (dSO : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr out, 32⟩)
    (dSA : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr sp, 4⟩)
    (dOA : Region.Disjoint ⟨State.addr out, 32⟩ ⟨State.addr sp, 4⟩)
    (lo : ∀ r ∈ finWr st out ++ finRd sp, (lowR sp 624).Disjoint r)
    (fS : st.toNat + 96 ≤ 2 ^ 32) (fO : out.toNat + 32 ≤ 2 ^ 32) :
    (Spec.Sha256.finalizeContract abi 624).pre (s.callEntry.withRegions (finRd sp) (finWr st out)) := by
  subst hspE
  sig_pre [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.a0]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  exact ⟨hsp, hsa, rfl, rfl, dSO, dSA, dOA, lo _ (by simp [State.addr]), lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), fS, fO⟩

theorem fin_pub {s₁ s₂ : State} (h₁ : FinArgs s₁ st out cnt) (h₂ : FinArgs s₂ st out cnt)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Sha256.finalizeContract abi 624).pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r2, h₁.r3, h₁.a0, h₂.r0, h₂.r2, h₂.r3, h₂.a0]
  exact ⟨hsp, trivial, trivial, trivial, trivial⟩

theorem fin_post {t : State} (h : FinArgs s st out cnt) {rd wr : List Region}
    (hp : (Spec.Sha256.finalizeContract abi 624).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr))
    {iv : Spec.Sha256.HashValue} {msg : List Byte} (hr : Spec.Sha256.ReprFrom iv s.mem (State.addr st) msg)
    (hl : msg.length = cnt) :
    Spec.Rsa.bytesAt t.mem (State.addr out) 32 = Spec.Sha256.finalHash iv msg := by
  sig_post [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost, abi, argRegs,
    reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r2, h.r3, h.a0] at hp
  exact hp iv msg hr (by rw [count_eq h.cnt32, hl])

end

/-! ## HMAC-SHA-256's `init(inner, outer, key, key_len)` -/

/-- The call's arguments. -/
structure HiArgs (s : State) (inn out key : BitVec 32) (kl : Nat) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = out
  r2 : s.gpr .r2 = key
  r3 : s.gpr .r3 = BitVec.ofNat 32 kl
  kl64 : kl ≤ 64

abbrev hiRd (key : BitVec 32) (kl : Nat) : List Region := [⟨State.addr key, kl⟩]
abbrev hiWr (inn out : BitVec 32) : List Region := [⟨State.addr inn, 96⟩, ⟨State.addr out, 96⟩]

section
variable {s : State} {inn out key : BitVec 32} {kl : Nat}

theorem hi_pre {sp : BitVec 32} (h : HiArgs s inn out key kl) (hspE : s.sp = sp) (hsp : 1656 ≤ sp.toNat)
    (dIO : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr out, 96⟩)
    (dIK : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr key, kl⟩)
    (dOK : Region.Disjoint ⟨State.addr out, 96⟩ ⟨State.addr key, kl⟩)
    (lo : ∀ r ∈ hiWr inn out ++ hiRd key kl, (lowR sp 1656).Disjoint r)
    (fI : inn.toNat + 96 ≤ 2 ^ 32) (fO : out.toNat + 96 ≤ 2 ^ 32) (fK : key.toNat + kl ≤ 2 ^ 32) :
    (Spec.Hmac.sha256I.initAnyKeyContract abi 1656).pre (s.callEntry.withRegions (hiRd key kl) (hiWr inn out)) := by
  subst hspE
  have k32 : kl < 2 ^ 32 := by have := h.kl64; omega_using [this]
  sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [h.r0, h.r1, h.r2, h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32]
  exact ⟨hsp, by have := s.sp.isLt; omega_using [], rfl, rfl, dIO, dIK, dOK, lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), lo _ (by simp [State.addr]), fI, fO, fK⟩

theorem hi_pub {s₁ s₂ : State} (h₁ : HiArgs s₁ inn out key kl) (h₂ : HiArgs s₂ inn out key kl)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Hmac.sha256I.initAnyKeyContract abi 1656).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3]
  exact ⟨hsp, trivial, trivial, trivial, trivial⟩

theorem hi_post {t : State} (h : HiArgs s inn out key kl) {rd wr : List Region}
    (hp : (Spec.Hmac.sha256I.initAnyKeyContract abi 1656).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr)) :
    let k0 := Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Rsa.bytesAt s.mem (State.addr key) kl)
    Spec.Sha256.Repr t.mem (State.addr inn) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
      Spec.Sha256.Repr t.mem (State.addr out) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) := by
  have k32 : kl < 2 ^ 32 := by have := h.kl64; omega_using [this]
  sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [h.r0, h.r1, h.r2, h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32] at hp
  exact hp

end

/-! ## HMAC-SHA-256's `finalize(inner, outer, count, out)` -/

/-- The call's arguments. -/
structure HfArgs (s : State) (inn ou out : BitVec 32) (cnt : Nat) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = ou
  r2 : s.gpr .r2 = BitVec.ofNat 32 cnt
  r3 : s.gpr .r3 = 0
  a0 : stackArg s 0 = out
  cnt32 : cnt < 2 ^ 32

abbrev hfRd (sp ou : BitVec 32) : List Region := [⟨State.addr ou, 96⟩, ⟨State.addr sp, 4⟩]
abbrev hfWr (inn out : BitVec 32) : List Region := [⟨State.addr inn, 96⟩, ⟨State.addr out, 32⟩]

section
variable {s : State} {inn ou out : BitVec 32} {cnt : Nat}

theorem hf_pre {sp : BitVec 32} (h : HfArgs s inn ou out cnt) (hspE : s.sp = sp) (hsp : 880 ≤ sp.toNat)
    (hsa : sp.toNat + 4 ≤ 2 ^ 32)
    (dIU : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr ou, 96⟩)
    (dIO : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr out, 32⟩)
    (dIA : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr sp, 4⟩)
    (dUO : Region.Disjoint ⟨State.addr ou, 96⟩ ⟨State.addr out, 32⟩)
    (dOA : Region.Disjoint ⟨State.addr out, 32⟩ ⟨State.addr sp, 4⟩)
    (lo : ∀ r ∈ hfWr inn out ++ hfRd sp ou, (lowR sp 880).Disjoint r)
    (fI : inn.toNat + 96 ≤ 2 ^ 32) (fU : ou.toNat + 96 ≤ 2 ^ 32) (fO : out.toNat + 32 ≤ 2 ^ 32) :
    (Spec.Hmac.sha256I.finalizeContract abi 880).pre (s.callEntry.withRegions (hfRd sp ou) (hfWr inn out)) := by
  subst hspE
  sig_pre [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.r1, h.a0]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  exact ⟨hsp, hsa, rfl, rfl, dIU, dIO, dIA, dUO, dOA, lo _ (by simp [State.addr]), lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), lo _ (by simp [State.addr]), fI, fU, fO⟩

theorem hf_pub {s₁ s₂ : State} (h₁ : HfArgs s₁ inn ou out cnt) (h₂ : HfArgs s₂ inn ou out cnt)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Hmac.sha256I.finalizeContract abi 880).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.a0, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.a0]
  exact ⟨hsp, trivial, trivial, trivial, trivial, trivial⟩

theorem hf_post {t : State} (h : HfArgs s inn ou out cnt) {rd wr : List Region}
    (hp : (Spec.Hmac.sha256I.finalizeContract abi 880).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr))
    {k0 text : List Byte} (hk : k0.length = 64) (ht : 64 + text.length = cnt)
    (hi : Spec.Sha256.Repr s.mem (State.addr inn) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text))
    (ho : Spec.Sha256.Repr s.mem (State.addr ou) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    Spec.Rsa.bytesAt t.mem (State.addr out) 32 = Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 k0 text := by
  sig_post [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r1, h.r2, h.r3, h.a0] at hp
  have c32 := h.cnt32
  exact hp k0 text hk (by omega_using [hk, ht, c32]) hi (by rw [count_eq h.cnt32, ← ht]) ho

end

end VG.Proof.RsaPkcs1Enc.Arm

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: `DH = SHA256(D)`

SHA-256's `init`, `update` with `D` and `finalize` to `scratch + sDH`, each
after the block of its arguments (`hashD_vp`): `DH`, the SHA-256 digest of
`D` (`H6`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- A stack argument of a call, in the frame's word `4 i`. -/
theorem stackArg_fr {σ s : State} (hs : S P σ s) {i : Nat} (hi : i < 16) :
    stackArg s i = s.mem.readW (P.lay.fr (4 * i)) 32 := by
  simp only [stackArg, stackArgAddr, hs.2.sp]
  rw [hs.1.ok.addrB (EP.lt_lay _ (by simp only [frameBytes]; omega_arith))]

/-- The bytes of a region of `scratch` kept while memory changes in the frame. -/
theorem sc_keep_fr {σ : State} (h : In P σ) {m m' : Mem} {d k o n : Nat} (hd : d + k ≤ frameBytes)
    (hn : o + n ≤ 8448) (hf : Frame [⟨P.lay.fr d, k⟩] m m') :
    Spec.Rsa.bytesAt m' (sc P o n).base n = Spec.Rsa.bytesAt m (sc P o n).base n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.fr_sc (by show d + k ≤ frameBytes + 56; omega_arith) hn).symm) (by omega_arith)

theorem repr_keep_fr {σ : State} (h : In P σ) {m m' : Mem} {d k o : Nat} (hd : d + k ≤ frameBytes)
    (ho : o + 96 ≤ 8448) (hf : Frame [⟨P.lay.fr d, k⟩] m m') {msg : List Byte}
    (hr : Spec.Sha256.Repr m (sc P o 96).base msg) : Spec.Sha256.Repr m' (sc P o 96).base msg :=
  repr_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.fr_sc (by show d + k ≤ frameBytes + 56; omega_arith) ho).symm) hr

theorem sc0 (P : EP) : (sc P 0 96).base = State.addr P.scr := BitVec.add_zero _

theorem sc0R (P : EP) (n : Nat) : sc P 0 n = ⟨State.addr P.scr, n⟩ := by simp [sc]

/-! ## The stages -/

/-- Before `init`. -/
def H1 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ s.gpr .r0 = P.scr

/-- After `init`. -/
def H2 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ Spec.Sha256.Repr s.mem (sc P 0 96).base []

/-- Before `update`. -/
def H3 (P : EP) (σ s : State) : Prop :=
  H2 P σ s ∧ UpdArgs s P.scr (P.scr + BitVec.ofNat 32 sD) P.K 0

/-- After `update`. -/
def H4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Sha256.Repr s.mem (sc P 0 96).base (Dfull P σ)

/-- Before `finalize`. -/
def H5 (P : EP) (σ s : State) : Prop := H4 P σ s ∧ FinArgs s P.scr (P.scr + BitVec.ofNat 32 sDH) P.K

/-- `DH`. -/
def H6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sDH 32).base 32 = Spec.Sha256.hash (Dfull P σ)

theorem shaInitArgs_wp {σ s : State} (h : D4 P σ s) : WP isa (.block shaInitArgs) s (H1 P σ) := by
  have hs := h.1.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => WP.block_nil ⟨?_, ?_⟩
  · have mm : t2.mem = s.mem := by rw [u2.mem, u1.mem]
    obtain ⟨⟨_, rc, pr, sl⟩, dd⟩ := h
    exact ⟨⟨⟨hs.1, s2⟩, rc, by rw [Priv, mm]; exact pr, by rw [mm]; exact sl⟩, by rw [mm]; exact dd⟩
  · rw [u2.gpr]; rfl

theorem scr96 {σ : State} (h : In P σ) : (P.scr.toNat + 96 ≤ 2 ^ 32) := by
  have := h.scr_fit; have := h.sl8; omega_arith

theorem shaInit_vp : VP (H1 P) (.call decFns.initN decFns.initC) (H2 P) := by
  refine hashCall initV (Nat.le_trans initS (by decide)) [] [⟨State.addr P.scr, 96⟩] (fun _ _ h => h.1.1.1)
    (fun _ s h => shInit_pre h.2 (scr96 h.1.1.1.1)) (fun _ s h => ?_)
    (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.1.1.1.1.subW0 (by decide))
    (fun _ _ _ _ h₁ h₂ => shInit_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.2.sp, h₂.1.1.1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · have w := In.scW0 h.1.1.1 (n := 96) (by decide)
    exact ⟨w.right, w⟩
  · obtain ⟨⟨hb, dd⟩, hr0⟩ := h
    have hs := hb.1
    have hK := hs.1.k1024
    refine ⟨⟨hb.after st fr fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.subW0 (by decide)
    · rw [← dd]
      refine bytesAt_frame fr (fun r hr => ?_) (by omega_arith)
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := sc_sep (P := P) (o := sD) (n := P.K) (o' := 0) (n' := 96) (by simp only [sD]; omega_arith)
          (by simp only [sD]; omega_arith) (by decide)
        rwa [sc0R] at this
      · exact (hs.1.low_sc (by simp only [sD]; omega_arith)).symm
    · rw [sc0]; exact shInit_post hr0 po
theorem In.lowR_sub {σ : State} (_h : In P σ) {S : Nat} (hS : S ≤ 3440) :
    Region.Sub (lowR P.B S) P.lay.LOW :=
  Offset.sub_below _ (by show S ≤ 3440; omega_arith) (by show 3440 - S + S ≤ 3440; omega_arith)

theorem In.lowR_sc {σ : State} (h : In P σ) {S o n : Nat} (hS : S ≤ 3440) (hn : o + n ≤ 8448) (ho : o < 8448) :
    (lowR P.B S).Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩ := by
  rw [h.scrA ho]; exact (h.low_sc hn).sub_left (h.lowR_sub hS)

theorem In.lowR_sc0 {σ : State} (h : In P σ) {S n : Nat} (hS : S ≤ 3440) (hn : n ≤ 8448) :
    (lowR P.B S).Disjoint ⟨State.addr P.scr, n⟩ := by
  rw [← sc0R]; exact (h.low_sc (by omega_arith)).sub_left (h.lowR_sub hS)

theorem In.lowR_fr {σ : State} (h : In P σ) {S n : Nat} (hS : S ≤ 3440) (hn : n ≤ frameBytes) :
    (lowR P.B S).Disjoint ⟨State.addr P.B, n⟩ := by
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0]; exact (Lay.fr_low (by simp only [frameBytes] at hn; omega_arith)).symm.sub_left (h.lowR_sub hS)

theorem In.sc_fr0 {σ : State} (h : In P σ) {o n k : Nat} (hn : o + n ≤ 8448) (ho : o < 8448) (hk : k ≤ frameBytes) :
    Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩ ⟨State.addr P.B, k⟩ := by
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0, h.scrA ho]; exact (h.fr_sc (by show 0 + k ≤ frameBytes + 56; omega_arith) hn).symm

theorem In.sc0_fr0 {σ : State} (h : In P σ) {n k : Nat} (hn : n ≤ 8448) (hk : k ≤ frameBytes) :
    Region.Disjoint ⟨State.addr P.scr, n⟩ ⟨State.addr P.B, k⟩ := by
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0, ← sc0R]; exact (h.fr_sc (by show 0 + k ≤ frameBytes + 56; omega_arith) (by omega_arith)).symm

theorem In.sc_sepW {σ : State} (h : In P σ) {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o)
    (h₁ : o + n ≤ 8448) (h₂ : o' + n' ≤ 8448) (ho : o < 8448) (ho' : o' < 8448) :
    Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩ ⟨State.addr (P.scr + BitVec.ofNat 32 o'), n'⟩ := by
  rw [h.scrA ho, h.scrA ho']; exact sc_sep hs h₁ h₂

theorem In.sc0_sepW {σ : State} (h : In P σ) {n o' n' : Nat} (hs : n ≤ o') (h₁ : n ≤ 8448)
    (h₂ : o' + n' ≤ 8448) (ho' : o' < 8448) :
    Region.Disjoint ⟨State.addr P.scr, n⟩ ⟨State.addr (P.scr + BitVec.ofNat 32 o'), n'⟩ := by
  rw [← sc0R, h.scrA ho']; exact sc_sep (.inl (by omega_arith)) (by omega_arith) h₂

theorem shaUpdArgs_wp {σ s : State} (h : H2 P σ s) : WP isa (.block shaUpdArgs) s (H3 P σ) := by
  obtain ⟨⟨hb, dd⟩, rp⟩ := h
  have hs := hb.1
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_strFr (d := 4) (by show 4 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u5.other _ (by decide), m4.gpr, u3.other _ (by decide), u2.other _ (by decide), r12])
    fun t6 s6 m6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => WP.block_nil ?_
  have s8 : P.lay.St σ t8 := (s6.of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have mm : t8.mem = (t1.mem.writeW (P.lay.fr 0) (t3.gpr .r1)).writeW (P.lay.fr 4) (t5.gpr .r1) := by
    rw [u8.mem, u7.mem, m6.mem, u5.mem, m4.mem, u3.mem, u2.mem]
  have fr : Frame [⟨P.lay.fr 0, 8⟩] s.mem t8.mem := by
    rw [mm, u1.mem]
    refine Frame.sub (rs := [⟨P.lay.fr 0, 4⟩, ⟨P.lay.fr 4, 4⟩]) ?_ fun r hr => ?_
    · exact ((Frame.refl _ _).writeW List.mem_cons_self (t3.gpr .r1) (Region.contains_self _ _)).writeW
        (List.mem_cons_of_mem _ List.mem_cons_self) (t5.gpr .r1) (Region.contains_self _ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have r1v : t3.gpr .r1 = P.scr + BitVec.ofNat 32 sD := by rw [u3.gpr, dpVal, u2.gpr]; rfl
  refine ⟨⟨⟨hb.frame s8 fr fun r hr => ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, by have := hs.1.k64; omega_arith, by decide⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · rw [sc_keep_fr hs.1 (by decide) (by simp only [sD]; omega_arith) fr]; exact dd
  · exact repr_keep_fr hs.1 (by decide) (by decide) fr rp
  · rw [u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u8.other _ (by decide), u7.gpr]
  · exact u8.gpr
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, r1v]
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u5.gpr]; rfl

theorem shaUpd_vp : VP (H3 P) (.call decFns.updN decFns.updC) (H4 P) := by
  refine hashCall updV (Nat.le_trans updS (by decide)) (updRd P.B (P.scr + BitVec.ofNat 32 sD) P.K)
    (updWr P.scr) (fun _ _ h => h.1.1.1.1) (fun _ s h => ?_) (fun _ s h => ?_)
    (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.1.1.1.1.1.subW0 (by decide))
    (fun _ _ _ _ h₁ h₂ => upd_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.1.2.sp, h₂.1.1.1.1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · have hs := h.1.1.1.1
    have hK := hs.1.k1024
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    refine upd_pre h.2 hs.2.sp (by have := hs.1.ok.B56; simp only at this; omega_arith)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega_arith)
      (hs.1.sc0_sepW (by decide) (by decide) (by simp only [sD]; omega_arith) (by decide))
      (hs.1.sc0_fr0 (by decide) (by decide)) (fun r hr => ?_) (scr96 hs.1)
      (hs.1.fit_sc (by simp only [sD]; omega_arith) (by decide))
    simp only [updWr, updRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) (by simp only [sD]; omega_arith) (by decide)
    · exact hs.1.lowR_fr (by decide) (by decide)
  · have hs := h.1.1.1.1
    have hK := hs.1.k1024
    have w := In.scW0 hs (n := 96) (by decide)
    refine ⟨Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) w.right, w⟩
    · exact (In.scW hs (by simp only [sD]; omega_arith) (by decide)).right
    · exact (In.frW hs (n := 8) (by decide)).right
  · obtain ⟨⟨⟨hb, dd⟩, rp⟩, ua⟩ := h
    have hs := hb.1
    have hK := hs.1.k1024
    refine ⟨hb.after st fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.subW0 (by decide)
    · have := upd_post ua po (iv := Spec.Sha256.H0) (msg := []) (by rw [← sc0]; exact rp) rfl
      rw [hs.1.scrA (by decide), show State.addr P.scr + BitVec.ofNat 64 sD = (sc P sD P.K).base from rfl, dd,
        List.nil_append] at this
      rw [sc0]; exact this

theorem shaFinArgs_wp {σ s : State} (h : H4 P σ s) : WP isa (.block shaFinArgs) s (H5 P σ) := by
  obtain ⟨hb, rp⟩ := h
  have hs := hb.1
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ?_
  have s6 : P.lay.St σ t6 := s5.of_rest (u6.rest (ws := [.r3]) (by simp)) u6.mem
  have mm : t6.mem = t1.mem.writeW (P.lay.fr 0) (t3.gpr .r1) := by rw [u6.mem, u5.mem, m4.mem, u3.mem, u2.mem]
  have fr : Frame [⟨P.lay.fr 0, 4⟩] s.mem t6.mem := by
    rw [mm, u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨⟨hb.frame s6 fr fun r hr => ?_, repr_keep_fr hs.1 (by decide) (by decide) fr rp⟩, ?_, ?_, ?_, ?_, by omega_arith⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · rw [u6.other _ (by decide), u5.other _ (by decide), m4.gpr, u3.other _ (by decide), u2.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · exact u6.gpr
  · rw [stackArg_fr ⟨hs.1, s6⟩ (by decide), mm, Mem.readW_writeW_self32, u3.gpr, dpVal, u2.gpr]; rfl

theorem shaFin_vp : VP (H5 P) (.call decFns.finN decFns.finC) (H6 P) := by
  refine hashCall finV (Nat.le_trans finS (by decide)) (finRd P.B)
    (finWr P.scr (P.scr + BitVec.ofNat 32 sDH)) (fun _ _ h => h.1.1.1) (fun _ s h => ?_) (fun _ s h => ?_)
    (fun _ _ h r hr => ?_)
    (fun _ _ _ _ h₁ h₂ => fin_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.2.sp, h₂.1.1.1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · have hs := h.1.1.1
    have hK := hs.1.k1024
    refine fin_pre h.2 hs.2.sp (by have := hs.1.ok.B56; simp only at this; omega_arith)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega_arith)
      (hs.1.sc0_sepW (by decide) (by decide) (by decide) (by decide))
      (hs.1.sc0_fr0 (by decide) (by decide)) (hs.1.sc_fr0 (by decide) (by decide) (by decide))
      (fun r hr => ?_) (scr96 hs.1) (hs.1.fit_sc (by decide) (by decide))
    simp only [finWr, finRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) (by decide) (by decide)
    · exact hs.1.lowR_fr (by decide) (by decide)
  · have hs := h.1.1.1
    have w : Covers (finWr P.scr (P.scr + BitVec.ofNat 32 sDH)) s.wr :=
      (In.scW0 hs (n := 96) (by decide)).cons (In.scW hs (by decide) (by decide))
    exact ⟨Covers.append_left (Covers.cons (In.frW hs (n := 4) (by decide)).right Covers.nil) w.right, w⟩
  · have hs := h.1.1.1
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.subW0 (by decide)
    · exact hs.1.subW (by decide) (by decide)
  · obtain ⟨⟨hb, rp⟩, fa⟩ := h
    have hs := hb.1
    have hK := hs.1.k1024
    refine ⟨hb.after st fr fun r hr => ?_, ?_⟩
    · simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.subW0 (by decide)
      · exact hs.1.subW (by decide) (by decide)
    · have hl : (Dfull P σ).length = P.K := by simp [bytesAt_length]; have := hs.1.dlK; omega_arith
      have := fin_post fa po (iv := Spec.Sha256.H0) (by rw [← sc0]; exact rp) hl
      rw [hs.1.scrA (by decide)] at this
      exact this

end VG.Proof.RsaPkcs1Enc.Arm.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: `KDK = HMAC(DH, C)`

HMAC-SHA-256's `init` with the key `DH`, SHA-256's `update` of the inner
state with the ciphertext, and HMAC's `finalize` to `scratch + sKDK`
(`K6`): the key derivation key of the draft's step 3.1 (`kdkV`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ 64 < key.length := by omega_using [h]
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega_using [h]

/-- The key derivation key. -/
abbrev kdkV (P : EP) (σ : State) : List Byte := Spec.RsaPkcs1Enc.kdk P.K (dB P σ) (cB P σ)

/-- `K₀` for the key `k`. -/
abbrev k0Of (k : List Byte) : List Byte := Spec.Hmac.blockKey Spec.Hmac.sha256 k

/-- HMAC's states after `init` with the key `k`, and the inner one after
`text`. -/
def Macd (m : Mem) (P : EP) (k text : List Byte) : Prop :=
  Spec.Sha256.Repr m (State.addr P.scr) (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.ipad ++ text) ∧
    Spec.Sha256.Repr m (State.addr (P.scr + BitVec.ofNat 32 sOuter)) (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.opad)

/-- `DH`. -/
abbrev dhV (P : EP) (σ : State) : List Byte := Spec.Sha256.hash (Dfull P σ)

/-! ## The stages -/

/-- Before `init`. -/
def K1 (P : EP) (σ s : State) : Prop :=
  H6 P σ s ∧ HiArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 sDH) 32

/-- After `init`. -/
def K2 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) []

/-- Before `update`. -/
def K3 (P : EP) (σ s : State) : Prop := K2 P σ s ∧ UpdArgs s P.scr P.inp P.K 64

/-- After `update`. -/
def K4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) (cB P σ)

/-- Before `finalize`. -/
def K5 (P : EP) (σ s : State) : Prop :=
  K4 P σ s ∧ HfArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 sKDK) (64 + P.K)

/-- `KDK`. -/
def K6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ

/-! ## Memory kept -/

theorem macd_frame {σ : State} (h : In P σ) {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sc P 0 192).Disjoint r) {k text : List Byte} (hm : Macd m P k text) : Macd m' P k text := by
  have s0 : Region.Sub ⟨State.addr P.scr, 96⟩ (sc P 0 192) := by
    rw [← sc0R]; exact Offset.sub _ (by decide) (by decide)
  have s1 : Region.Sub ⟨State.addr (P.scr + BitVec.ofNat 32 sOuter), 96⟩ (sc P 0 192) := by
    rw [h.scrA (by decide)]; exact Offset.sub _ (by decide) (by decide)
  exact ⟨repr_frame hf (fun r hr => (hd r hr).sub_left s0) hm.1, repr_frame hf (fun r hr => (hd r hr).sub_left s1) hm.2⟩

/-- The calls' stack arguments are in the frame's first 8 bytes. -/
theorem frame8 {s t : State} {va vb : BitVec 32}
    (h : t.mem = (s.mem.writeW (P.lay.fr 0) va).writeW (P.lay.fr 4) vb) :
    Frame [⟨P.lay.fr 0, 8⟩] s.mem t.mem := by
  rw [h]
  refine Frame.sub (rs := [⟨P.lay.fr 0, 4⟩, ⟨P.lay.fr 4, 4⟩]) ?_ fun r hr => ?_
  · exact ((Frame.refl _ _).writeW List.mem_cons_self va (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) vb (Region.contains_self _ _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩

theorem frame4 {s t : State} {va : BitVec 32} (h : t.mem = s.mem.writeW (P.lay.fr 0) va) :
    Frame [⟨P.lay.fr 0, 4⟩] s.mem t.mem := by
  rw [h]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The pieces -/

theorem macInitArgs_wp {σ s : State} {key : Nat} (hk : key < 256) {G : State → State → Prop}
    (hs : S P σ s) (hG : ∀ t, P.lay.St σ t → t.mem = s.mem →
      HiArgs t P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 key) 32 → G σ t) :
    WP isa (.block (macInitArgs key)) s (G σ) := by
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [hk])))
    fun t4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun t5 u5 => WP.block_nil ?_
  have s5 : P.lay.St σ t5 := ((s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r2]) (by simp)) u4.mem).of_rest (u5.rest (ws := [.r3]) (by simp)) u5.mem
  refine hG t5 s5 (by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]) ⟨?_, ?_, ?_, u5.gpr, by decide⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide), u2.gpr]; rfl

/-- HMAC's `init` with the 32-byte key at `scratch + key`, keeping what `keep`
says of the memory outside HMAC's states and the stack below. -/
theorem macInit_vp {key : Nat} (hk : 192 ≤ key) (hk' : key + 32 ≤ 8448) {F G : State → State → Prop}
    (hF : ∀ σ s, F σ s → S P σ s ∧ HiArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 key) 32)
    (hG : ∀ σ s t, F σ s → P.lay.St σ t → Frame [sc P 0 192, P.lay.LOW] s.mem t.mem →
      Macd t.mem P (Spec.Rsa.bytesAt s.mem (sc P key 32).base 32) [] → G σ t) :
    VP F (.call decFns.hiN decFns.hiC) G := by
  refine hashCall hiV (Nat.le_trans hiS (by decide)) (hiRd (P.scr + BitVec.ofNat 32 key) 32)
    (hiWr P.scr (P.scr + BitVec.ofNat 32 sOuter)) (fun σ s h => (hF σ s h).1) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun σ s h r hr => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => hi_pub (hF _ _ h₁).2 (hF _ _ h₂).2 (by rw [(hF _ _ h₁).1.2.sp, (hF _ _ h₂).1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · obtain ⟨hs, ha⟩ := hF σ s h
    refine hi_pre ha hs.2.sp (Nat.le_trans (by decide : 1656 ≤ 3440) hs.1.ok.B56)
      (hs.1.sc0_sepW (by decide) (by decide) (by decide) (by decide))
      (hs.1.sc0_sepW (by omega_using [hk]) (by decide) hk' (by omega_using [hk']))
      (hs.1.sc_sepW (.inl (by simp only [sOuter]; omega_using [hk])) (by decide) hk' (by decide) (by omega_using [hk'])) (fun r hr => ?_)
      (scr96 hs.1)
      (hs.1.fit_sc (by decide) (by decide)) (hs.1.fit_sc hk' (by omega_using [hk']))
    simp only [hiWr, hiRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) hk' (by omega_using [hk'])
  · have hs := (hF σ s h).1
    have w : Covers (hiWr P.scr (P.scr + BitVec.ofNat 32 sOuter)) s.wr :=
      (In.scW0 hs (n := 96) (by decide)).cons (In.scW hs (by decide) (by decide))
    exact ⟨Covers.append_left (Covers.cons (In.scW hs hk' (by omega_using [hk'])).right Covers.nil) w.right, w⟩
  · have hs := (hF σ s h).1
    simp only [hiWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.subW0 (by decide)
    · exact hs.1.subW (by decide) (by decide)
  · obtain ⟨hs, ha⟩ := hF σ s h
    have fr' : Frame [sc P 0 192, P.lay.LOW] s.mem s'.mem := fr.sub fun r hr => by
      simp only [hiWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by rw [sc0R]; exact Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., by rw [hs.1.scrA (by decide)]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    refine hG σ s s' h st fr' ?_
    have := hi_post ha po
    rw [hs.1.scrA (by omega_using [hk'])] at this
    exact ⟨by rw [List.append_nil]; exact this.1, this.2⟩

/-- What `update` needs of the data, `dl` bytes at `dp`. -/
structure DataOk (P : EP) (s : State) (dp : BitVec 32) (dl : Nat) : Prop where
  cov : Covers [⟨State.addr dp, dl⟩] (s.rd ++ s.wr)
  dS : Region.Disjoint ⟨State.addr P.scr, 96⟩ ⟨State.addr dp, dl⟩
  lo : (lowR P.B 624).Disjoint ⟨State.addr dp, dl⟩
  fit : dp.toNat + dl ≤ 2 ^ 32

/-- SHA-256's `update` of HMAC's inner state, after `init`, with the `dl`
bytes at `dp`. -/
theorem macUpd_vp {dp : BitVec 32} {dl : Nat} {F G : State → State → Prop} {k : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧ UpdArgs s P.scr dp dl 64 ∧ Macd s.mem P (k σ s) [] ∧ DataOk P s dp dl ∧
      (k σ s).length ≤ 64)
    (hG : ∀ σ s t, F σ s → P.lay.St σ t → Frame [sc P 0 96, P.lay.LOW] s.mem t.mem →
      Macd t.mem P (k σ s) (Spec.Rsa.bytesAt s.mem (State.addr dp) dl) → G σ t) :
    VP F (.call decFns.updN decFns.updC) G := by
  refine hashCall updV (Nat.le_trans updS (by decide)) (updRd P.B dp dl) (updWr P.scr)
    (fun σ s h => (hF σ s h).1) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ s h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (hF σ s h).1.1.subW0 (by decide))
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => upd_pub (hF _ _ h₁).2.1 (hF _ _ h₂).2.1
      (by rw [(hF _ _ h₁).1.2.sp, (hF _ _ h₂).1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · obtain ⟨hs, ua, -, dk, -⟩ := hF σ s h
    refine upd_pre ua hs.2.sp (Nat.le_trans (by decide : 624 ≤ 3440) hs.1.ok.B56)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega_using [this]) dk.dS
      (hs.1.sc0_fr0 (by decide) (by decide)) (fun r hr => ?_) (scr96 hs.1) dk.fit
    simp only [updWr, updRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact dk.lo
    · exact hs.1.lowR_fr (by decide) (by decide)
  · obtain ⟨hs, -, -, dk, -⟩ := hF σ s h
    have w := In.scW0 hs (n := 96) (by decide)
    exact ⟨Covers.append_left (dk.cov.cons (Covers.cons (In.frW hs (n := 8) (by decide)).right Covers.nil))
      w.right, w⟩
  · obtain ⟨hs, ua, md, -, hk⟩ := hF σ s h
    have fr' : Frame [sc P 0 96, P.lay.LOW] s.mem s'.mem := by rw [sc0R]; exact fr
    refine hG σ s s' h st fr' ⟨?_, ?_⟩
    · have := upd_post ua po (iv := Spec.Sha256.H0) (msg := Spec.Hmac.xorPad (k0Of (k σ s)) Spec.Hmac.ipad)
        (by have := md.1; rwa [List.append_nil] at this)
        (by rw [Proof.Hmac.Common.xorPad_length, blockKey_length hk])
      exact this
    · refine repr_frame fr' (fun r hr => ?_) md.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hs.1.scrA (by decide)]; exact sc_sep (.inr (by decide)) (by decide) (by decide)
      · rw [hs.1.scrA (by decide)]; exact (hs.1.low_sc (by decide)).symm

/-- HMAC's `finalize` to the 32 bytes at `scratch + o`. -/
theorem macFin_vp {o tl : Nat} (ho : 192 ≤ o) (ho' : o + 32 ≤ 8448) {F G : State → State → Prop}
    {k text : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧
      HfArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 o) (64 + tl) ∧
      Macd s.mem P (k σ s) (text σ s) ∧ (k σ s).length ≤ 64 ∧ (text σ s).length = tl)
    (hG : ∀ σ s t, F σ s → P.lay.St σ t → Frame [sc P 0 96, sc P o 32, P.lay.LOW] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (sc P o 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 (k σ s) (text σ s) → G σ t) :
    VP F (.call decFns.hfN decFns.hfC) G := by
  refine hashCall hfV (Nat.le_trans hfS (by decide)) (hfRd P.B (P.scr + BitVec.ofNat 32 sOuter))
    (hfWr P.scr (P.scr + BitVec.ofNat 32 o)) (fun σ s h => (hF σ s h).1) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun σ s h r hr => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => hf_pub (hF _ _ h₁).2.1 (hF _ _ h₂).2.1 (by rw [(hF _ _ h₁).1.2.sp, (hF _ _ h₂).1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · obtain ⟨hs, ha, -, -, -⟩ := hF σ s h
    refine hf_pre ha hs.2.sp (Nat.le_trans (by decide : 880 ≤ 3440) hs.1.ok.B56)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega_using [this])
      (hs.1.sc0_sepW (by decide) (by decide) (by decide) (by decide))
      (hs.1.sc0_sepW (by omega_using [ho]) (by decide) ho' (by omega_using [ho'])) (hs.1.sc0_fr0 (by decide) (by decide))
      (hs.1.sc_sepW (.inl (by simp only [sOuter]; omega_using [ho])) (by decide) ho' (by decide) (by omega_using [ho']))
      (hs.1.sc_fr0 ho' (by omega_using [ho']) (by decide)) (fun r hr => ?_) (scr96 hs.1)
      (hs.1.fit_sc (by decide) (by decide)) (hs.1.fit_sc ho' (by omega_using [ho']))
    simp only [hfWr, hfRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) ho' (by omega_using [ho'])
    · exact hs.1.lowR_sc (by decide) (by decide) (by decide)
    · exact hs.1.lowR_fr (by decide) (by decide)
  · have hs := (hF σ s h).1
    have w : Covers (hfWr P.scr (P.scr + BitVec.ofNat 32 o)) s.wr :=
      (In.scW0 hs (n := 96) (by decide)).cons (In.scW hs ho' (by omega_using [ho']))
    exact ⟨Covers.append_left ((In.scW hs (by decide) (by decide)).right.cons
      (Covers.cons (In.frW hs (n := 4) (by decide)).right Covers.nil)) w.right, w⟩
  · have hs := (hF σ s h).1
    simp only [hfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.subW0 (by decide)
    · exact hs.1.subW ho' (by omega_using [ho'])
  · obtain ⟨hs, ha, md, hk, ht⟩ := hF σ s h
    have fr' : Frame [sc P 0 96, sc P o 32, P.lay.LOW] s.mem s'.mem := by
      rw [sc0R, show sc P o 32 = ⟨State.addr (P.scr + BitVec.ofNat 32 o), 32⟩ by rw [hs.1.scrA (by omega_using [ho'])]]
      exact fr
    refine hG σ s s' h st fr' ?_
    have := hf_post ha po (blockKey_length hk) (by rw [ht]) md.1 md.2
    rw [hs.1.scrA (by omega_using [ho'])] at this
    exact this

/-! ## `KDK` -/

theorem kdkUpdArgs_wp {σ s : State} (h : K2 P σ s) : WP isa (.block kdkUpdArgs) s (K3 P σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 9) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_strFr (d := 4) (by show 4 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u5.other _ (by decide), m4.gpr, u3.other _ (by decide), u2.other _ (by decide), r12])
    fun t6 s6 m6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => WP.block_nil ?_
  have s8 : P.lay.St σ t8 := (s6.of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have mm : t8.mem = (s.mem.writeW (P.lay.fr 0) (t3.gpr .r1)).writeW (P.lay.fr 4) (t5.gpr .r1) := by
    rw [u8.mem, u7.mem, m6.mem, u5.mem, m4.mem, u3.mem, u2.mem, u1.mem]
  have fr := frame8 mm
  refine ⟨⟨hb.frame s8 fr fun r hr => ?_, macd_frame hs.1 fr (fun r hr => ?_) md⟩, ?_, ?_, ?_, ?_, ?_,
    by have := hs.1.k1024; omega_using [this], by decide⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hs.1.fr_sc (by decide) (by decide)).symm
  · rw [u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u8.other _ (by decide), u7.gpr]
  · exact u8.gpr
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, u3.gpr]; rfl
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u5.gpr]; rfl

theorem kdkFinArgs_wp {σ s : State} (h : K4 P σ s) : WP isa (.block kdkFinArgs) s (K5 P σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => WP.block_nil ?_
  have s8 : P.lay.St σ t8 := (s6.of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have mm : t8.mem = s.mem.writeW (P.lay.fr 0) (t3.gpr .r1) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, m4.mem, u3.mem, u2.mem, u1.mem]
  have fr := frame4 mm
  have r0v : t2.gpr .r0 = P.scr := by rw [u2.gpr]; rfl
  refine ⟨⟨hb.frame s8 fr fun r hr => ?_, macd_frame hs.1 fr (fun r hr => ?_) md⟩, ?_, ?_, ?_, ?_, ?_,
    by omega_using [hK]⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hs.1.fr_sc (by decide) (by decide)).symm
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), r0v]
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr, dpVal, m4.gpr,
      u3.other _ (by decide), r0v]
  · rw [u8.other _ (by decide), u7.gpr, dpVal, u6.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [EP.argv, List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using []
  · exact u8.gpr
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u3.gpr, dpVal, r0v]

theorem hash_length (x : List Byte) : (Spec.Sha256.hash x).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

theorem kdkInit_vp : VP (K1 P) (.call decFns.hiN decFns.hiC) (K2 P) :=
  macInit_vp (key := sDH) (by decide) (by decide) (fun _ _ h => ⟨h.1.1.1, h.2⟩) fun σ s t h st fr md => by
    obtain ⟨⟨hb, dh⟩, -⟩ := h
    have hs := hb.1
    refine ⟨hb.frame st fr fun r hr => ?_, by rw [dh] at md; exact md⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.safe_sc (by decide)
    · exact hs.1.safe_low

theorem In.dataINP {σ s : State} (hs : S P σ s) : DataOk P s P.inp P.K :=
  { cov := In.roR hs (R := P.INP) (by simp)
    dS := by rw [← sc0R]; exact hs.1.sc_ro (by decide) (R := P.INP) (by simp)
    lo := (hs.1.ok.low_buf (R := P.INP) (.inl (by simp))).sub_left (hs.1.lowR_sub (by decide))
    fit := by have := hs.1.ok.fits P.INP (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this }

theorem kdkUpd_vp : VP (K3 P) (.call decFns.updN decFns.updC) (K4 P) :=
  macUpd_vp (k := fun σ _ => dhV P σ) (fun _ _ h => ⟨h.1.1.1, h.2, h.1.2, In.dataINP h.1.1.1,
    by rw [hash_length]; decide⟩) fun σ s t h st fr md => by
    obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1
    refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.safe_sc (by decide)
      · exact hs.1.safe_low
    · rw [hs.2.ro (R := P.INP) (by simp)] at md; exact md

theorem kdkV_eq (P : EP) {σ : State} (h : In P σ) :
    kdkV P σ = Spec.Hmac.hmac Spec.Hmac.sha256 (dhV P σ) (cB P σ) := by
  simp only [kdkV, Spec.RsaPkcs1Enc.kdk, dhV, Dfull]
  rw [VG.Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by rw [bytesAt_length]; exact h.dlK), bytesAt_length]

theorem kdkFin_vp : VP (K5 P) (.call decFns.hfN decFns.hfC) (K6 P) :=
  macFin_vp (o := sKDK) (tl := P.K) (k := fun σ _ => dhV P σ) (text := fun σ _ => cB P σ) (by decide) (by decide)
    (fun _ _ h => ⟨h.1.1.1, h.2, h.1.2, by rw [hash_length]; decide, bytesAt_length _ _ _⟩)
    fun σ s t h st fr hk => by
    obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1
    refine ⟨hb.frame st fr fun r hr => ?_, by rw [hk, kdkV_eq P hs.1]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.safe_sc (by decide)
    · exact hs.1.safe_sc (by decide)
    · exact hs.1.safe_low

end VG.Proof.RsaPkcs1Enc.Arm.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the stages of an IRPRF block

An IRPRF loop (`Prf`): its label, the code of its bit length, its output's
length and place in `scratch`, its number of blocks, and bytes of `scratch`
it keeps. Before block `i` (`CI`): the call's result, `KDK`, the bytes kept,
the number of blocks in its slot, and the first `i` blocks. The stages of a
block (`B0` … `B9`), and the blocks of code between its calls.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg op2_lsl dpVal)
open VG.Proof.RsaPkcs1Enc (prfBlock)

variable {P : EP}

/-- An IRPRF loop: the label's bytes `vs`, the code `len` of the bit length,
the output's length `L`, its place `dst` in `scratch`, its number `nb` of
blocks, and the `xn` bytes `xv` at `scratch + xo` it keeps. -/
structure Prf (P : EP) where
  vs : List Nat
  len : List Instr
  L : Nat
  dst : Nat
  nb : Nat
  xo : Nat
  xn : Nat
  xv : State → List Byte
  vs_lt : ∀ v ∈ vs, v < 256
  vs_len : vs.length + 4 ≤ 16
  nb1 : 1 ≤ nb
  nb_le : nb ≤ 256
  dst_lo : 272 ≤ dst
  dst_hi : dst + 32 * nb ≤ 8448
  dst_enc : VG.Arm.encodable (BitVec.ofNat 32 dst) = true
  x_lo : 208 ≤ xo
  x_hi : xo + xn ≤ 8448
  x_sep : xo + xn ≤ dst ∨ dst + 32 * nb ≤ xo
  lenOk : ∀ {σ s t : State} {i : Nat}, S P σ s → s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg →
    s.gpr .r3 = BitVec.ofNat 32 P.K → MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
    ∀ {Q : State → Prop}, (∀ t', MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 4) t' → Q t') →
      WP isa (.block len) t Q

namespace Prf

variable (R : Prf P)

/-- The label. -/
abbrev lab : List Byte := R.vs.map (BitVec.ofNat 8)

/-- The length of a block's message. -/
abbrev tl : Nat := R.vs.length + 4

end Prf

/-- Before block `i`. -/
structure CI (P : EP) (R : Prf P) (i : Nat) (σ s : State) : Prop where
  hi : i ≤ R.nb
  base : Base P σ s
  kdk : Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ
  x : Spec.Rsa.bytesAt s.mem (sc P R.xo R.xn).base R.xn = R.xv σ
  sNB : s.mem.readW (P.lay.fr oNB) 32 = BitVec.ofNat 32 R.nb
  blk : Spec.Rsa.bytesAt s.mem (sc P R.dst (32 * i)).base (32 * i) =
    (List.range i).flatMap (prfBlock (kdkV P σ) R.lab R.L)

/-- What the loop's writes stay apart from. -/
structure Keep (P : EP) (R : Prf P) (i : Nat) (r : Region) : Prop where
  safe : Safe P r
  kdk : (sc P sKDK 32).Disjoint r
  x : (sc P R.xo R.xn).Disjoint r
  blk : (sc P R.dst (32 * i)).Disjoint r
  nb : Region.Disjoint ⟨P.lay.fr oNB, 4⟩ r

section
variable {R : Prf P} {i : Nat} {σ s t : State}

theorem CI.keep (h : CI P R i σ s) (st : P.lay.St σ t) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hk : ∀ r ∈ rs, Keep P R i r) : CI P R i σ t where
  hi := h.hi
  base := h.base.frame st hf fun r hr => (hk r hr).safe
  kdk := (bytes_frame hf (R := sc P sKDK 32) (fun r hr => (hk r hr).kdk) (by show 32 ≤ 2 ^ 64; decide)).trans h.kdk
  x := (bytes_frame hf (R := sc P R.xo R.xn) (fun r hr => (hk r hr).x)
    (by have := R.x_hi; show R.xn ≤ 2 ^ 64; omega_arith)).trans h.x
  sNB := by
    rw [hf.readW (r := ⟨P.lay.fr oNB, 4⟩) (Region.contains_self _ _) (fun r hr => (hk r hr).nb) (by decide)]
    exact h.sNB
  blk := (bytes_frame hf (R := sc P R.dst (32 * i)) (fun r hr => (hk r hr).blk)
    (by have := R.dst_hi; have := h.hi; show 32 * i ≤ 2 ^ 64; omega_arith)).trans h.blk

theorem CI.of_mem (h : CI P R i σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : CI P R i σ t :=
  h.keep st (rs := []) (by rw [hm]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil

theorem CI.S (h : CI P R i σ s) : S P σ s := h.base.1

/-- A slot of the frame kept. -/
theorem slot_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr d, 4⟩ r) : m'.readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

namespace In
variable (h : In P σ)
include h

theorem keep_sc {o n : Nat} (hn : o + n ≤ 8448) (hk : o + n ≤ sKDK ∨ sKDK + 32 ≤ o)
    (hx : o + n ≤ R.xo ∨ R.xo + R.xn ≤ o) (hb : o + n ≤ R.dst ∨ R.dst + 32 * i ≤ o) (hi : i ≤ R.nb) :
    Keep P R i (sc P o n) where
  safe := h.safe_sc hn
  kdk := sc_sep (by simp only [sKDK] at hk ⊢; omega_arith) (by decide) hn
  x := sc_sep (by omega_arith) R.x_hi hn
  blk := sc_sep (by omega_arith) (by have := R.dst_hi; omega_arith) hn
  nb := h.fr_sc (by simp only [oNB, frameBytes]; decide) hn

theorem keep_low (hi : i ≤ R.nb) : Keep P R i P.lay.LOW where
  safe := h.safe_low
  kdk := (h.low_sc (by decide)).symm
  x := (h.low_sc R.x_hi).symm
  blk := (h.low_sc (by have := R.dst_hi; omega_arith)).symm
  nb := Lay.fr_low (by simp only [oNB]; decide)

theorem keep_fr {d n : Nat} (hd : d + n ≤ frameBytes) (ho : d + n ≤ oR ∨ oR + 4 ≤ d)
    (hnb : d + n ≤ oNB ∨ oNB + 4 ≤ d) (hi : i ≤ R.nb) : Keep P R i ⟨P.lay.fr d, n⟩ where
  safe := h.safe_fr hd ho
  kdk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega_arith) (by decide)).symm
  x := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega_arith) R.x_hi).symm
  blk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega_arith) (by have := R.dst_hi; omega_arith)).symm
  nb := Lay.fr_sep (by simp only [oNB] at hnb ⊢; omega_arith) (by decide) (by simp only [frameBytes] at hd; omega_arith)

/-- The data of `update` in `scratch`. -/
theorem dataSc {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) (ho : 96 ≤ o) (ho8 : o < 8448) :
    DataOk P s (P.scr + BitVec.ofNat 32 o) n where
  cov := (In.scW hs hn (by omega_arith)).right
  dS := h.sc0_sepW ho (by decide) hn (by omega_arith)
  lo := h.lowR_sc (by decide) hn (by omega_arith)
  fit := h.fit_sc hn (by omega_arith)

end In

end

/-! ## The stages of block `i` -/

section
variable (P : EP) (R : Prf P) (i : Nat) (σ s : State)

/-- Block `i` begins: its counter in its slot. -/
def B0 : Prop := CI P R i σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

/-- The message's place, `i` and `k`. -/
def B1 : Prop :=
  B0 P R i σ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg ∧ s.gpr .r1 = BitVec.ofNat 32 i ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K

/-- The message written. -/
def B2 : Prop := B0 P R i σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L

/-- Before HMAC's `init`. -/
def B3 : Prop := B2 P R i σ s ∧ HiArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 sKDK) 32

/-- After it. -/
def B4 : Prop := B2 P R i σ s ∧ Macd s.mem P (kdkV P σ) []

/-- Before `update`. -/
def B5 : Prop := B4 P R i σ s ∧ UpdArgs s P.scr (P.scr + BitVec.ofNat 32 sMsg) R.tl 64

/-- After it. -/
def B6 : Prop := B0 P R i σ s ∧ Macd s.mem P (kdkV P σ) (msgV i R.lab R.L)

/-- Before `finalize`. -/
def B7 : Prop :=
  B6 P R i σ s ∧ HfArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 (R.dst + 32 * i))
    (64 + R.tl)

/-- Block `i` written. -/
def B8 : Prop := CI P R (i + 1) σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

/-- The counter incremented. -/
def B9 : Prop :=
  CI P R (i + 1) σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 (i + 1) ∧
    s.gpr .r1 = BitVec.ofNat 32 (i + 1) ∧ s.gpr .r2 = BitVec.ofNat 32 R.nb

end

/-! ## The blocks of code -/

section
variable {R : Prf P} {i : Nat} {σ s : State}

theorem msgPtr_wp (h : B0 P R i σ s) : WP isa (.block msgPtr) s (B1 P R i σ) := by
  have hs := h.1.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => WP.block_nil ?_
  have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have mm : t5.mem = s.mem := by rw [u5.mem, u4.mem, m3]
  refine ⟨⟨h.1.of_mem s5 mm, by rw [mm]; exact h.2⟩, ?_, ?_, u5.gpr⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.gpr, m3, h.2]

theorem msgBytes_b2 (h : B1 P R i σ s) (hi : i < 256) :
    WP isa (.block (msgBytes R.vs R.len)) s (B2 P R i σ) := by
  obtain ⟨⟨hc, sI⟩, r0, r1, r3⟩ := h
  have hs := hc.S
  refine WP.mono (msgBytes_wp (L := R.L) hs r0 r1 hi R.vs_len R.vs_lt (R.lenOk hs r0 r3)) fun t ⟨st, fr, _, hb⟩ => ?_
  have hk : ∀ r ∈ [sc P sMsg 16], Keep P R i r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.keep_sc (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sMsg]; omega_arith))
      (.inl (by have := R.dst_lo; simp only [sMsg]; omega_arith)) hc.hi
  refine ⟨⟨hc.keep st.2 fr hk, ?_⟩, hb⟩
  rw [slot_keep fr fun r hr => ?_]
  · exact sI
  · simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by decide)

theorem B2.msg_frame (h : B2 P R i σ s) {t : State} {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (sc P sMsg R.tl).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L :=
  (bytes_frame hf hd (by have := R.vs_len; show R.vs.length + 4 ≤ 2 ^ 64; omega_arith)).trans h.2

theorem B0.keep (h : B0 P R i σ s) {t : State} (st : P.lay.St σ t) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hk : ∀ r ∈ rs, Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) : B0 P R i σ t :=
  ⟨h.1.keep st hf fun r hr => (hk r hr).1, by rw [slot_keep hf fun r hr => (hk r hr).2]; exact h.2⟩

theorem prfUpdArgs_wp (h : B4 P R i σ s) : WP isa (.block (prfUpdArgs (R.vs.length + 4))) s (B5 P R i σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1.1.S
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine wp_mov (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith)))
    fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_strFr (d := 4) (by show 4 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u5.other _ (by decide), m4.gpr, u3.other _ (by decide), u2.other _ (by decide), r12])
    fun t6 s6 m6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => WP.block_nil ?_
  have s8 : P.lay.St σ t8 := (s6.of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have mm : t8.mem = (s.mem.writeW (P.lay.fr 0) (t3.gpr .r1)).writeW (P.lay.fr 4) (t5.gpr .r1) := by
    rw [u8.mem, u7.mem, m6.mem, u5.mem, m4.mem, u3.mem, u2.mem, u1.mem]
  have fr := frame8 mm
  have hfr : ∀ r ∈ [(⟨P.lay.fr 0, 8⟩ : Region)], Region.Disjoint (sc P 0 192) r ∧ (sc P sMsg R.tl).Disjoint r ∧
      (Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hs.1.fr_sc (by decide) (by decide)).symm, (hs.1.fr_sc (by decide) (by simp only [sMsg]; omega_arith)).symm,
      hs.1.keep_fr (by decide) (by simp only [oR]; decide) (by simp only [oNB]; decide) hb.1.1.hi,
      Lay.fr_sep (by simp only [oI]; decide) (by decide) (by decide)⟩
  have r1v : t3.gpr .r1 = P.scr + BitVec.ofNat 32 sMsg := by rw [u3.gpr, dpVal, u2.gpr]; rfl
  refine ⟨⟨⟨hb.1.keep s8 fr fun r hr => (hfr r hr).2.2, hb.msg_frame fr fun r hr => (hfr r hr).2.1⟩,
    macd_frame hs.1 fr (fun r hr => (hfr r hr).1) md⟩, ?_, ?_, u8.gpr, ?_, ?_, by omega_arith, by decide⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u8.other _ (by decide), u7.gpr]
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, r1v]
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u5.gpr]

theorem shl5 (i : Nat) : BitVec.ofNat 32 i <<< 5 = BitVec.ofNat 32 (32 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem prfFinArgs_wp (h : B6 P R i σ s) :
    WP isa (.block (prfFinArgs (R.vs.length + 4) R.dst)) s (B7 P R i σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1.S
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide) fun t3 s3 u3 => ?_
  refine wp_dp (op2_imm R.dst_enc) fun t4 u4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := (s3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem).of_rest
    (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), r12])
    fun t6 s6 m6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith)))
    fun t8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t9 u9 => WP.block_nil ?_
  have s9 : P.lay.St σ t9 := ((s6.of_rest (u7.rest (ws := [.r1]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r2]) (by simp)) u8.mem).of_rest (u9.rest (ws := [.r3]) (by simp)) u9.mem
  have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have mm : t9.mem = s.mem.writeW (P.lay.fr 0) (t5.gpr .r1) := by
    rw [u9.mem, u8.mem, u7.mem, m6.mem, u5.mem, u4.mem, m3]
  have fr := frame4 mm
  have r0v : t2.gpr .r0 = P.scr := by rw [u2.gpr]; rfl
  have hfr : ∀ r ∈ [(⟨P.lay.fr 0, 4⟩ : Region)], Region.Disjoint (sc P 0 192) r ∧
      (Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hs.1.fr_sc (by decide) (by decide)).symm,
      hs.1.keep_fr (by decide) (by simp only [oR]; decide) (by simp only [oNB]; decide) hb.1.hi,
      Lay.fr_sep (by simp only [oI]; decide) (by decide) (by decide)⟩
  have r1v : t5.gpr .r1 = P.scr + BitVec.ofNat 32 (R.dst + 32 * i) := by
    rw [u5.gpr, dpVal, u4.gpr, dpVal, u3.other _ (by decide), r0v, u4.other _ (by decide), u3.gpr, u2.mem, u1.mem, hb.2,
      shl5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨⟨hb.keep s9 fr fun r hr => (hfr r hr).2, macd_frame hs.1 fr (fun r hr => (hfr r hr).1) md⟩, ?_, ?_, ?_,
    u9.gpr, ?_, by omega_arith⟩
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), r0v]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, dpVal, m6.gpr, u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), r0v]
  · rw [u9.other _ (by decide), u8.gpr]
  · rw [stackArg_fr ⟨hs.1, s9⟩ (by decide), mm, Mem.readW_writeW_self32, r1v]

theorem incr_wp (h : B8 P R i σ s) : WP isa (.block incr) s (B9 P R i σ) := by
  obtain ⟨hc, sI⟩ := h
  have hs := hc.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine s4.wp_slot (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) (by decide) fun t5 s5 u5 => WP.block_nil ?_
  have r1v : t3.gpr .r1 = BitVec.ofNat 32 (i + 1) := by
    rw [u3.gpr, dpVal, u2.gpr, u1.mem, sI, BitVec.ofNat_add_ofNat]
  have mm : t5.mem = s.mem.writeW (P.lay.fr oI) (t3.gpr .r1) := by
    rw [u5.mem, m4.mem, u3.mem, u2.mem, u1.mem]
  have fr : Frame [⟨P.lay.fr oI, 4⟩] s.mem t5.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc' := hc.keep s5 fr fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.keep_fr (by decide) (by simp only [oR, oI]; decide) (by simp only [oNB, oI]; decide) hc.hi
  refine ⟨hc', by rw [mm, Mem.readW_writeW_self32, r1v], by rw [u5.other _ (by decide), m4.gpr, r1v], ?_⟩
  rw [u5.gpr, ← u5.mem]; exact hc'.sNB

end

end VG.Proof.RsaPkcs1Enc.Arm.Dec
