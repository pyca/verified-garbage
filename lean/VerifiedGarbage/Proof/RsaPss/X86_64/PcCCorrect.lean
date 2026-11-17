module

public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Spec.RsaPss.MdTable

/-! ### `RsaPss.X86_64.PrecomputedCtx`, which only this module used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on x86-64: the
precondition

`Pre` is `VPre`, which names the facts of `verifyK.pre`, the cache `pre` of
the public key's values among them; `preR` and `argsR` are its region and the
stack arguments'.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

variable (tsH tsG : List FnTable)

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩

/-- All ten stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- The precondition, by name. -/
abbrev Pre (s : State) : Prop := VPre tsH tsG s

variable {tsH tsG}

theorem Pre.toVPre {s : State} (h : Pre tsH tsG s) : VPre tsH tsG s := h

theorem pre_of {s : State} (h : (verifyK tsH tsG).pre s) : Pre tsH tsG s := VPre.of tsH tsG h

theorem Pre.argsScr {s : State} (h : Pre tsH tsG s) :
    (argsR s).Disjoint (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) := h.dsa.symm

theorem Pre.argsStack {s : State} (h : Pre tsH tsG s) : (argsR s).Disjoint (vstkR s) := h.dKa.symm

theorem Pre.preScr {s : State} (h : Pre tsH tsG s) :
    (preR s).Disjoint (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) := h.dsp.symm

theorem Pre.preStack {s : State} (h : Pre tsH tsG s) : (preR s).Disjoint (vstkR s) := h.dKp.symm

end VG.Proof.RsaPss.X86_64.Pc

end

end

/-! ### `RsaPss.X86_64.PcChk`, which this module and modules that import it used -/

section

/-! ### `RsaPss.X86_64.PrecomputedArgs`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

variable {tsH tsG : List FnTable}

theorem arg_read {s u : State} (hp : Pre tsH tsG s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 10) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [hrd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem arg_keep {s : State} {m : Mem} (hp : Pre tsH tsG s) (hf : Frame (vwrR s) s.mem m) {j : Nat} (hj : j < 10) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.argsStack
    · exact hp.argsScr

theorem load_pre {s t : State} (hp : Pre tsH tsG s) (hsp : t.gpr .rsp = fb s) (hrd : t.rd = s.rd)
    (hf : Frame (vwrR s) s.mem t.mem) :
    WP isa (.block [.mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧
        u.gpr .rdx = stackArg s 6 ∧ u.gpr .rcx = stackArg s 7 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [arg, ea_sp, hsp, arg_read hp hrd (show 6 < 10 by decide), arg_read hp hrd (show 7 < 10 by decide),
    arg_keep hp hf (show 6 < 10 by decide), arg_keep hp hf (show 7 < 10 by decide)]

end VG.Proof.RsaPss.X86_64.Pc

end

end

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: the call of `checkEncoding`

`chkArgs` stores to `sAcc` whether the first `lo` bytes of the public-key
operation's output are zero (all ones if so), and `checkEncoding`'s
arguments: the digest, the last `emLen` bytes of the output, `emBits`, the
salt length's arguments, and the working space after the output
(`chkArgs_ok`); `checkEncoding` then runs under its contract and returns
whether the encoding is consistent, the frame and the output kept
(`chk_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {tsH tsG : List FnTable}

def cA1 : List Instr :=
  [.mov .rcx (.mem (sp sScr)), .movzx8 .r9 (at_ .rcx), .mov .r10 (.mem (sp sLo)), .mov32 .r11 (.imm 0),
    .alu .sub .r11 (.reg .r10), .alu .and .r9 (.reg .r11), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
    .store (sp sAcc) .r9]

/-- `sAcc`: all ones if the first `lo ≤ 1` bytes are zero. -/
def accV (lo : Nat) (b : Byte) : BitVec 64 := if lo = 0 ∨ b = 0 then BitVec.allOnes 64 else 0

theorem cA1_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lo : Nat} (h26 : W 26 = BitVec.ofNat 64 lo) (hlo : lo ≤ 1) :
    WP isa (.block cA1) u fun u' => Keep [.rcx, .r9, .r10, .r11] u u' ∧
      u'.mem = u.mem.writeW (off F sAcc) (accV lo (V 0)) ∧ u'.gpr .rcx = S ∧ u'.gpr .r10 = BitVec.ofNat 64 lo := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  obtain h0 : u.mem S = V 0 := by have := R.scr 0 (by decide); rwa [off_zero] at this
  obtain hl0 : InRegions (u.rd ++ u.wr) S 1 := by have := L.sld8 (d := 0) (by decide); rwa [off_zero] at this
  refine WP.mono (WP.keep [.rcx, .r9, .r10, .r11] (Q := fun u' =>
      u'.mem = u.mem.writeW (off F sAcc) (accV lo (V 0)) ∧ u'.gpr .rcx = S ∧ u'.gpr .r10 = BitVec.ofNat 64 lo) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [cA1, ea_sp, ea_at0, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sLo) (by decide),
    L.st (d := sAcc) (by decide), hs, hl0, h0, R.rd (d := sLo) 26 rfl (by decide), h26]
  refine congrArg (u.mem.writeW (off F sAcc)) ?_
  generalize V 0 = b
  rcases (show lo = 0 ∨ lo = 1 by omega_using [hlo]) with rfl | rfl
  · revert b; decide
  · revert b; decide

def cA2 : List Instr :=
  [.mov .rdi (.mem (sp sDig)), .mov .rsi (.reg .rcx), .alu .add .rsi (.reg .r10), .mov .rdx (.mem (sp sEml)),
    .mov .r8 (.mem (arg 2)), .mov .r9 (.mem (arg 3))]

def cA3 : List Instr :=
  [.mov .rax (.mem (sp sK)), .alu .add .rax (.imm 7), .shift .shr .rax 3, .mov .r10 (.mem (sp sScrLen)),
    .alu .sub .r10 (.reg .rax), .store (sp 8) .r10, .shift .shl .rax 3, .alu .add .rax (.reg .rcx),
    .store (sp 0) .rax]

def cA4 : List Instr :=
  [.mov .rax (.mem (arg 8)), .store (sp 16) .rax, .mov .rax (.mem (arg 9)), .store (sp 24) .rax]

def cA5 : List Instr := [.mov .rcx (.mem (sp sBits))]

theorem chkArgs_eq : chkArgs = cA1 ++ cA2 ++ cA3 ++ cA4 ++ cA5 := rfl

/-- A write to the frame keeps what `Frame (vwrR s)` says. -/
theorem vframe_w {s : State} (hp : Pre tsH tsG s) {m m' : Mem} (hf : Frame (vwrR s) m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame (vwrR s) m (m'.writeW (off (fb s) d) v) := by
  obtain hF := vfb_toNat hp.toVPre
  have := hp.sp2
  exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self (frR s)) v
    (Offset.contains_base _ (by unfold frameBytes at *; omega_using [hd]) (by unfold frameBytes at *; omega_using [hd]))).sub
    fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩)

/-- The tables to `checkEncoding`'s stack arguments 2 and 3. -/
theorem cA4_ok {s u : State} (hp : Pre tsH tsG s) {S : Addr} (L : Lay u (fb s) S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem) :
    WP isa (.block cA4) u fun u' => Lay u' (fb s) S ∧ Keep [.rax] u u' ∧
      Rep u'.mem (fb s) S V (upd (upd W 2 (stackArg s 8)) 3 (stackArg s 9)) ∧ Frame (vwrR s) s.mem u'.mem := by
  have G' := L.geo
  obtain R1 := R.wf G' (k := 2) (by decide) (stackArg s 8)
  obtain R2 := R1.wf G' (k := 3) (by decide) (stackArg s 9)
  rw [show off (fb s) (8 * 2) = off (fb s) 16 from rfl] at R1 R2
  rw [show off (fb s) (8 * 3) = off (fb s) 24 from rfl] at R2
  obtain hM1 := vframe_w hp hM (d := 16) (by decide) (stackArg s 8)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = (u.mem.writeW (off (fb s) 16) (stackArg s 8)).writeW
      (off (fb s) 24) (stackArg s 9)) ?_ rfl) fun u' ⟨hm, k⟩ => ?_
  · xrun [cA4, arg, ea_sp, L.rsp, arg_read hp hrd (show 8 < 10 by decide), arg_read hp hrd (show 9 < 10 by decide),
      arg_keep hp hM (show 8 < 10 by decide), arg_keep hp hM1 (show 9 < 10 by decide),
      L.st (d := 16) (by decide), L.st (d := 24) (by decide)]
  obtain R' : Rep u'.mem (fb s) S V (upd (upd W 2 (stackArg s 8)) 3 (stackArg s 9)) := by rw [hm]; exact R2
  exact ⟨L.of_rep' R R' (by simp [upd]) (k.gpr (by decide)) k.2.2, k, R', by rw [hm]; exact vframe_w hp hM1 (by decide) _⟩

/-- `⌈k / 8⌉`, the words of the output. -/
def kw (k : Nat) : Nat := (k + 7) / 8

/-- The slots after `chkArgs`. -/
def chkW (W : Nat → BitVec 64) (s : State) (lo : Nat) (b : Byte) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd W 33 (accV lo b)) 1 (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))) 0
    (off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat))) 2 (stackArg s 8)) 3 (stackArg s 9)

theorem chkArgs_ok {s u : State} (hp : Pre tsH tsG s) (L : Lay u (fb s) (stackArg s 4)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 4) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem) {lo el eb : Nat}
    (h17 : W 17 = s.gpr .rsi) (h22 : W 22 = stackArg s 5) (h26 : W 26 = BitVec.ofNat 64 lo)
    (h27 : W 27 = BitVec.ofNat 64 eb) (h28 : W 28 = BitVec.ofNat 64 el) (h37 : W 37 = s.gpr .r8) (hlo : lo ≤ 1) :
    WP isa (.block chkArgs) u fun u' => Lay u' (fb s) (stackArg s 4) ∧
      Keep [.rcx, .r9, .r10, .r11, .rdi, .rsi, .rdx, .r8, .r9, .rax, .r10, .rcx] u u' ∧
      Rep u'.mem (fb s) (stackArg s 4) V (chkW W s lo (V 0)) ∧ Frame (vwrR s) s.mem u'.mem ∧
      u'.gpr .rdi = s.gpr .r8 ∧ u'.gpr .rsi = off (stackArg s 4) lo ∧ u'.gpr .rdx = BitVec.ofNat 64 el ∧
      u'.gpr .rcx = BitVec.ofNat 64 eb ∧ u'.gpr .r8 = stackArg s 2 ∧ u'.gpr .r9 = stackArg s 3 := by
  have G' := L.geo
  obtain hk1 := hp.k1; have hk2 := hp.k2
  set S := stackArg s 4
  rw [chkArgs_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16) (cA1_ok L R h26 hlo))
    fun u1 ⟨⟨k1, hm1, hcx1, h101⟩, f1⟩ => ?_
  obtain hM1 := vframe_keep hp.toVPre hw L.rsp hM f1
  obtain R1 := R.wf G' (k := 33) (by decide) (accV lo (V 0))
  rw [show off (fb s) (8 * 33) = off (fb s) sAcc from rfl, ← hm1] at R1
  obtain L1 : Lay u1 (fb s) S := L.of_rep' R R1 (by simp [upd]) (k1.gpr (by decide)) k1.2.2
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .r8, .r9] (Q := fun v => v.mem = u1.mem ∧ v.gpr .rdi = s.gpr .r8 ∧
      v.gpr .rsi = off S lo ∧ v.gpr .rdx = BitVec.ofNat 64 el ∧ v.gpr .r8 = stackArg s 2 ∧ v.gpr .r9 = stackArg s 3)
    ?_ rfl) fun v ⟨⟨hm2, hdi, hsi, hdx, h8, h9⟩, k2⟩ => ?_
  · xrun [cA2, arg, ea_sp, L1.rsp, L1.ld (d := sDig) (by decide), L1.ld (d := sEml) (by decide),
      R1.rd (d := sDig) 37 rfl (by decide), R1.rd (d := sEml) 28 rfl (by decide),
      arg_read hp (k1.2.1.trans hrd) (show 2 < 10 by decide), arg_read hp (k1.2.1.trans hrd) (show 3 < 10 by decide),
      arg_keep hp hM1 (show 2 < 10 by decide), arg_keep hp hM1 (show 3 < 10 by decide), hcx1, h101]
    simp [upd, h37, h28]
  obtain L2 : Lay v (fb s) S := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  obtain R2 : Rep v.mem (fb s) S V (upd W 33 (accV lo (V 0))) := by rw [hm2]; exact R1
  obtain Ra := R2.wf G' (k := 1) (by decide) (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))
  obtain Rb := Ra.wf G' (k := 0) (by decide) (off S (8 * kw (s.gpr .rsi).toNat))
  rw [show off (fb s) (8 * 1) = off (fb s) 8 from rfl] at Ra Rb
  rw [show off (fb s) (8 * 0) = fb s from off_zero _] at Rb
  obtain hst0 : InRegions v.wr (fb s) 8 := by simpa only [off_zero] using L2.st (d := 0) (by decide)
  obtain hcx2 : v.gpr .rcx = S := by rw [k2.gpr (by decide)]; exact hcx1
  obtain hM2 : Frame (vwrR s) s.mem v.mem := by rw [hm2]; exact hM1
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16) (WP.keep [.rax, .r10] (Q := fun y =>
      y.mem = (v.mem.writeW (off (fb s) 8) (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))).writeW (fb s)
      (off S (8 * kw (s.gpr .rsi).toNat))) ?_ rfl))
    fun y ⟨⟨hm3, k3⟩, f3⟩ => ?_
  · xrun [cA3, ea_sp, L2.rsp, L2.ld (d := sK) (by decide), L2.ld (d := sScrLen) (by decide),
      L2.st (d := 8) (by decide), hst0,
      R2.rd (d := sK) 17 rfl (by decide), R2.rd (d := sScrLen) 22 rfl (by decide), hcx2]
    obtain e1 : (s.gpr .rsi + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 = BitVec.ofNat 64 (kw (s.gpr .rsi).toNat) := by
      rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 from rfl]
      unfold kw
      generalize s.gpr .rsi = x at *
      bv_omega
    obtain e2 : BitVec.ofNat 64 (kw (s.gpr .rsi).toNat) <<< 3 + S = off S (8 * kw (s.gpr .rsi).toNat) := by
      rw [BitVec.add_comm]; simp only [off]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      unfold kw; rw [Nat.shiftLeft_eq]; omega_using []
    simp only [upd, Nat.reduceEqDiff, ite_false, h17, h22, e1, e2]
  obtain R3 : Rep y.mem (fb s) S V (upd (upd (upd W 33 (accV lo (V 0))) 1
      (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))) 0 (off S (8 * kw (s.gpr .rsi).toNat))) := by
    rw [hm3]; exact Rb
  obtain L3 : Lay y (fb s) S := L2.of_rep' R2 R3 (by simp [upd]) (k3.gpr (by decide)) k3.2.2
  obtain hM3 := vframe_keep hp.toVPre (k2.2.2.trans (k1.2.2.trans hw)) L2.rsp hM2 f3
  refine WP.mono (cA4_ok hp L3 R3 (k3.2.1.trans (k2.2.1.trans (k1.2.1.trans hrd))) hM3) fun z ⟨L4, k4, R4, hM4⟩ => ?_
  refine WP.mono (WP.keep [.rcx] (Q := fun w => w.mem = z.mem ∧ w.gpr .rcx = BitVec.ofNat 64 eb) ?_ rfl)
    fun w ⟨⟨hm5, hcx⟩, k5⟩ => ?_
  · xrun [cA5, ea_sp, L4.rsp, L4.ld (d := sBits) (by decide), R4.rd (d := sBits) 27 rfl (by decide)]
    simp [upd, h27]
  obtain R5 : Rep w.mem (fb s) S V (chkW W s lo (V 0)) := by rw [hm5]; exact R4
  obtain k35 : Keep [.rax, .r10, .rax, .rcx] v w := (k3.trans k4).trans k5
  refine ⟨L4.congr (k5.gpr (by decide)) k5.2.2 (by rw [hm5]), ((k1.trans k2).trans k35).mono (by decide), R5,
    by rw [hm5]; exact hM4, ?_, ?_, ?_, hcx, ?_, ?_⟩ <;>
    rw [k35.gpr (by decide)] <;> with_reducible assumption


/-! ## The call -/

/-- A table's word, read from memory that changed only in the writable
regions and below the frame. -/
theorem vtab_read {s : State} (hp : Pre tsH tsG s) {m : Mem} (hM : Frame (vwrR s) s.mem m) {i o : Nat}
    (hi : i = 8 ∨ i = 9) (ho : o + 8 ≤ 56) :
    m.readW (off (stackArg s i) o) 64 = s.mem.readW (off (stackArg s i) o) 64 := by
  obtain sH : Region.Sub ⟨stackArg s 8, 56⟩ ⟨stackArg s 8, 88⟩ := Region.sub_prefix (by decide)
  obtain sG : Region.Sub ⟨stackArg s 9, 56⟩ ⟨stackArg s 9, 88⟩ := Region.sub_prefix (by decide)
  obtain hw : (stackArg s i).toNat + 56 ≤ 2 ^ 64 := by rcases hi with rfl | rfl <;> [have := hp.wTH; have := hp.wTG] <;> omega_using [this]
  refine hM.readW (r := ⟨stackArg s i, 56⟩) (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])) (fun r hr => ?_) (by decide)
  simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hi with rfl | rfl <;> rcases hr with rfl | rfl
  · exact (hp.dKtH.sub_right sH).symm
  · exact (hp.dstH.sub_right sH).symm
  · exact (hp.dKtG.sub_right sG).symm
  · exact (hp.dstG.sub_right sG).symm

/-- The index of the table `hash`'s hash function, at word 5 of the table. -/
theorem vidx_read {s : State} (hp : Pre tsH tsG s) {m : Mem} (hM : Frame (vwrR s) s.mem m) :
    m.readW (off (stackArg s 8) 40) 64 = s.mem.readW (off (stackArg s 8) 40) 64 := by
  have hw := hp.wTH
  refine hM.readW (r := ⟨stackArg s 8, 88⟩) (Offset.contains_base _ (by omega_using []) (by omega_using [])) (fun r hr => ?_) (by decide)
  simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dKtH.symm
  · exact hp.dstH.symm

/-- The tables' words in a state whose memory changed only in the writable
regions and below the frame. -/
theorem TabsAt.vframe {T : Tabs} {s t : State} (hp : Pre tsH tsG s)
    (h : TabsAt T.H T.dn T.f T.G T.g (stackArg s 8) (stackArg s 9) s) (hM : Frame (vwrR s) s.mem t.mem)
    (hs : t.syms = s.syms) : TabsAt T.H T.dn T.f T.G T.g (stackArg s 8) (stackArg s 9) t :=
  ⟨by rw [vtab_read hp hM (.inl rfl) (by decide), hs]; exact h.h0, by rw [vtab_read hp hM (.inl rfl) (by decide), hs]; exact h.h3,
    by rw [vtab_read hp hM (.inl rfl) (by decide), hs]; exact h.h4, by rw [vtab_read hp hM (.inr rfl) (by decide), hs]; exact h.g0,
    by rw [vtab_read hp hM (.inr rfl) (by decide), hs]; exact h.g1, by rw [vtab_read hp hM (.inr rfl) (by decide), hs]; exact h.g2,
    by rw [vtab_read hp hM (.inr rfl) (by decide)]; exact h.g4, by rw [hs]; exact h.hf, by rw [hs]; exact h.gf⟩

variable (T : Tabs) in
/-- What `checkEncoding` reads: the digest, the encoding, the tables and its
stack arguments. -/
def kRd (s : State) (lo el : Nat) : List Region :=
  [⟨s.gpr .r8, T.H.D⟩, ⟨off (stackArg s 4) lo, el⟩, ⟨stackArg s 8, 56⟩, ⟨stackArg s 9, 56⟩, ⟨fb s, 32⟩]

/-- What it writes: its working space, after the output. -/
def kWr (s : State) : List Region :=
  [⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat),
    (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩]

theorem kw_le {k : Nat} : k ≤ 8 * kw k := by unfold kw; omega_using []

/-- What the call of `checkEncoding` needs of the state before it. -/
structure KAt (T : Tabs) (s t : State) (lo eb el : Nat) : Prop where
  sp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = frR s :: s.wr
  M : Frame (vwrR s) s.mem t.mem
  sy : t.syms = s.syms
  w0 : word t.mem (fb s) (8 * 0) = off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat)
  w1 : word t.mem (fb s) (8 * 1) = stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)
  w2 : word t.mem (fb s) (8 * 2) = stackArg s 8
  w3 : word t.mem (fb s) (8 * 3) = stackArg s 9
  di : t.gpr .rdi = s.gpr .r8
  si : t.gpr .rsi = off (stackArg s 4) lo
  dx : t.gpr .rdx = BitVec.ofNat 64 el
  cx : t.gpr .rcx = BitVec.ofNat 64 eb
  r8 : t.gpr .r8 = stackArg s 2
  r9 : t.gpr .r9 = stackArg s 3
  hlo : lo + el ≤ (s.gpr .rsi).toNat
  eb1 : 1 ≤ eb
  eb2 : eb ≤ Proof.RsaPss.maxEmBits
  hel : el = Spec.RsaPss.emLength eb
  hD : T.H.D = (s.gpr .r9).toNat
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 8) (stackArg s 9) s

theorem ck_pre {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} {s t : State} (hp : Pre tsH tsG s) {lo eb el : Nat}
    (E : KAt T s t lo eb el) :
    (chkK T Hs Gs).pre (t.callEntry.withRegions (kRd T s lo el) (kWr s)) := by
  have hsp := E.sp
  obtain hE0 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 0) (by decide)).trans E.w0
  obtain hE1 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 1) (by decide)).trans E.w1
  obtain hE2 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 2) (by decide)).trans E.w2
  obtain hE3 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 3) (by decide)).trans E.w3
  obtain hlo := E.hlo; have heb1 := E.eb1; have heb2 := E.eb2; have hel := E.hel
  obtain fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  obtain fSE : Frame (vwrR s) s.mem t.callEntry.mem := E.M.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
  obtain hTab : TabsAt T.H T.dn T.f T.G T.g (stackArg s 8) (stackArg s 9)
      (t.callEntry.withRegions (kRd T s lo el) (kWr s)) :=
    TabsAt.vframe (t := t.callEntry.withRegions (kRd T s lo el) (kWr s)) hp E.tabs fSE (E.sy ▸ rfl)
  simp only [chkK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    E.di, E.si, E.dx, E.cx, hsp, stackArgAddr_call hsp, hE0, hE1, hE2, hE3]
  obtain hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  have hcs : chkStack = 408 := rfl
  have c2 : oRsa = 8192 := rfl
  obtain h8' := vfb_sub8 hp.toVPre
  obtain hkw := kw_le (k := (s.gpr .rsi).toNat)
  obtain hkw2 : kw (s.gpr .rsi).toNat ≤ 128 := by unfold kw; omega_using [hk2]
  obtain hsc : (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 5).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega_using [hsl]
  obtain hel2 : el ≤ 1024 := by omega_using [hlo, hk2]
  obtain toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]
  obtain hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega_using [hlo]
  obtain heb' : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega_using [heb2]
  rw [hel', heb', E.hD]
  obtain hsk : (kw (s.gpr .rsi).toNat) * 8 ≤ (stackArg s 5).toNat * 8 := by unfold kw at *; omega_using [hsl]
  -- What lies in what.
  obtain sI : Region.Sub ⟨off (stackArg s 4) lo, el⟩ (vscrR s) := Offset.sub_base _ (by omega_using [hlo, hsl])
  obtain sR : Region.Sub ⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat),
      (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold kw at *; omega_using [hsl])
  obtain sA : Region.Sub ⟨fb s, 32⟩ (vstkR s) := fun a h => vframe_sub s a (Region.sub_prefix (by decide) a h)
  obtain sRet : Region.Sub ⟨fb s - 8, 8⟩ (vstkR s) := vret8_sub s
  obtain sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 chkStack, chkStack⟩ (vstkR s) := by
    simp only [vstkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain sH : Region.Sub ⟨stackArg s 8, 56⟩ ⟨stackArg s 8, 88⟩ := Region.sub_prefix (by decide)
  obtain sG : Region.Sub ⟨stackArg s 9, 56⟩ ⟨stackArg s 9, 88⟩ := Region.sub_prefix (by decide)
  obtain dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega_using [])).symm
  obtain dKA : (⟨fb s - 8 - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    refine Region.Disjoint.sub_left (Offset.base_disjoint_below (fb s) (n := 416) (k := 32) (by omega_using [])).symm ?_
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain dIR : (⟨off (stackArg s 4) lo, el⟩ : Region).Disjoint
      ⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat), (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega_using [hlo, hkw])) (by omega_using [hlo]) (by rw [hsc]; unfold kw at *; omega_using [wS])
  obtain hsA : (vscrR s).Disjoint ⟨fb s, 32⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by unfold chkStack; omega_arith, by omega_using [hF, this, h8'], by rw [kRd, E.hD], rfl,
    hp.ddgs.sub_right sR, dIR, hsA.sub_left sR,
    hp.dKdg.sub_left sRet, (hp.dKs.sub_left sRet).sub_right sI, (hp.dKs.sub_left sRet).sub_right sR, dRA,
    hp.dKdg.sub_left sStk, (hp.dKs.sub_left sStk).sub_right sI, (hp.dKs.sub_left sStk).sub_right sR, dKA,
    hp.wDg, by rw [toNat_off (by omega_using [hlo, hsl, wS])]; omega_using [hlo, hsl, wS], by rw [toNat_off (by omega_using [hsl, wS, hkw2]), hsc]; unfold kw at *; omega_using [hsl, wS],
    heb1, heb2, hel, by rw [hsc]; unfold Proof.RsaPss.encodingScratchWords kw at *; omega_using [hsl],
    (hp.dstH.sub_left sR).sub_right sH, (hp.dstG.sub_left sR).sub_right sG, (hp.dKtH.sub_left sRet).sub_right sH,
    (hp.dKtG.sub_left sRet).sub_right sG, (hp.dKtH.sub_left sStk).sub_right sH, (hp.dKtG.sub_left sStk).sub_right sG,
    by have := hp.wTH; omega_using [this], by have := hp.wTG; omega_using [this], hTab⟩

theorem ck_covers {T : Tabs} {s t : State} (hp : Pre tsH tsG s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    {lo el : Nat} (hlo : lo + el ≤ (s.gpr .rsi).toNat) (hD : T.H.D = (s.gpr .r9).toNat) :
    Covers (kRd T s lo el ++ kWr s) (t.rd ++ t.wr) ∧ Covers (kWr s) t.wr := by
  obtain hsl := hp.hsl; have hk2 := hp.k2
  obtain hsc : (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 5).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega_using [hsl]
  obtain hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  obtain hscr : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  obtain cw : Covers (kWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, hscr, 8 * kw (s.gpr .rsi).toNat, rfl, by dsimp only; rw [hsc]; unfold kw at *; omega_using [hsl]⟩
  obtain hin : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [hrd]; exact hx)
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [kRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, hin _ (by rw [hp.hrdE]; simp), 0, z _, by dsimp only; omega_using [hD]⟩
  · exact ⟨_, List.mem_append_right _ hscr, lo, rfl, by dsimp only; omega_using [hlo, hsl]⟩
  · exact ⟨⟨stackArg s 8, 88⟩, hin _ (by rw [hp.hrdE]; simp), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨⟨stackArg s 9, 88⟩, hin _ (by rw [hp.hrdE]; simp), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩

theorem ck_call {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} {chkN : String} {chkC : Prog isa}
    (hv : ∀ s, (chkK T Hs Gs).pre s → ∃ t s', Exec isa chkC s t s' ∧ abiPreserved s s' ∧ (chkK T Hs Gs).post s s')
    (hspC : SpSafe chkC) (hd : chkC.x86_64Depth ≤ chkStack)
    {s t : State} (hp : Pre tsH tsG s) {lo eb el : Nat} (E : KAt T s t lo eb el) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 4) V W) :
    WP isa (.call chkN chkC) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (vwrR s) s.mem t'.mem ∧ t'.syms = s.syms ∧
      Rep t'.mem (fb s) (stackArg s 4)
        (fun o => if inR [(8 * kw (s.gpr .rsi).toNat, oRsa - 8 * kw (s.gpr .rsi).toNat)] o then
          t'.mem (off (stackArg s 4) o) else V o) W ∧
      (t'.gpr .rax).setWidth 32 = if Spec.RsaPss.verifyEncoding Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .r8) T.H.D)
        (Spec.Rsa.bytesAt t.mem (off (stackArg s 4) lo) el) eb
        (Spec.RsaPss.expectedSaltLen (stackArg s 2) ((stackArg s 3).setWidth 32)) then 1 else 0 := by
  obtain hst := E.sp; have hrd := E.rd; have hwr := E.wr; have hM := E.M
  obtain hlo := E.hlo; have hel := E.hel; have heb2 := E.eb2
  obtain ⟨hc, hw⟩ := ck_covers (T := T) hp hrd hwr hlo E.hD
  refine X86_64.WP.of_syms (X86_64.WP.callF hv hspC (by unfold chkStack at hd; omega_using [hd])
    (ck_pre (Hs := Hs) (Gs := Gs) hp E) hc hw ?_)
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx hsy
  obtain hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  obtain hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  have c2 : oRsa = 8192 := rfl
  obtain hkw := kw_le (k := (s.gpr .rsi).toNat)
  obtain hkw2 : kw (s.gpr .rsi).toNat ≤ 128 := by unfold kw; omega_using [hk2]
  obtain hsc : (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 5).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega_using [hsl]
  rw [hst] at hf
  obtain sR : Region.Sub ⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat),
      (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold kw at *; omega_using [hsl])
  obtain sBel : Region.Sub (below (fb s) (chkC.x86_64Depth + 8)) (vstkR s) := by
    simp only [below, fb, vstkR, sub_sub']
    exact Offset.sub_below _ (by unfold chkStack at hd; omega_using [hd, h392, hvs]) (by unfold chkStack at hd; omega_using [hd, hvs])
  obtain dFb : (frR s).Disjoint (below (fb s) (chkC.x86_64Depth + 8)) :=
    Offset.base_disjoint_below (fb s) (by unfold chkStack at hd; omega_using [hd, h392])
  obtain hS8 : Region.Sub ⟨stackArg s 4, oRsa⟩ (vscrR s) := Region.sub_prefix (by omega_using [hsl, c2])
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), hsy.trans E.sy, ?_, ?_⟩
  · simp only [kWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sR⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · refine R.of_call hp.geo (fun x hx hin => hf x fun r hr hc => ?_) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'; dsimp only; omega_using [c2, hkw2])
    simp only [kWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rcases hin with hin | hin
      · refine hx _ (List.mem_singleton_self _) ?_
        obtain h1 := (Offset.lt_iff x (stackArg s 4) (d := 8 * kw (s.gpr .rsi).toNat)
          (n := (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8)
          (by rw [hsc]; unfold kw at *; omega_using [wS])).mp (by simp only [Region.Contains, off] at hc; omega_using [hc])
        obtain h2 : (x - stackArg s 4).toNat < oRsa := by simp only [Region.Contains] at hin; omega_using [hin]
        show (x - (stackArg s 4 + BitVec.ofNat 64 (8 * kw (s.gpr .rsi).toNat))).toNat + 1 ≤
          oRsa - 8 * kw (s.gpr .rsi).toNat
        have := (Offset.lt_iff x (stackArg s 4) (d := 8 * kw (s.gpr .rsi).toNat)
          (n := oRsa - 8 * kw (s.gpr .rsi).toNat) (by omega_using [c2, hkw2])).mpr ⟨h1.1, by omega_using [h2]⟩
        omega_using [this]
      · exact (hp.dKs.sub_left (vframe_sub s)) x hin (sR x hc)
    · rcases hin with hin | hin
      · exact hp.dKs x (sBel x hc) (hS8 x hin)
      · exact dFb x hin hc
  · have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    obtain fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
 rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
    obtain hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega_using [hlo]
    obtain heb' : (BitVec.ofNat 64 eb).toNat = eb := by
      rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega_using [heb2]
    simp only [chkK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      E.di, E.si, E.dx, E.cx, E.r8, E.r9, hg₂ .rax (by decide), hel', heb'] at hpost
    rw [E.hD] at hpost ⊢
    rw [bytesAt_frame fSE (p := s.gpr .r8) (len := (s.gpr .r9).toNat) (vin_apart hp.dKdg hp.ddgs)
        (by have := hp.wDg; omega_using []),
      bytesAt_frame fE (p := off (stackArg s 4) lo) (len := el) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ((hp.dKs.sub_left (vret8_sub s)).sub_right (Offset.sub_base _ (by omega_using [hlo, hsl]) :
          Region.Sub ⟨off (stackArg s 4) lo, el⟩ (vscrR s))).symm) (by omega_using [hlo])] at hpost
    exact hpost


end VG.Proof.RsaPss.X86_64.Pc

end

end

/-! ### `RsaPss.X86_64.PrecomputedCall`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

variable {tsH tsG : List FnTable}

def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 0, (s.gpr .rsi).toNat⟩, ⟨fb s, 32⟩]

/-- What the public-key operation writes: its output, at the start of
`scratch`, and its working space. -/
def cWr (s : State) : List Region :=
  [⟨stackArg s 4, (s.gpr .rsi).toNat⟩,
    ⟨off (stackArg s 4) oRsa, (stackArg s 5 - BitVec.ofNat 64 1024).toNat * 8⟩]

def validCache (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat)

theorem pre_words {s : State} {m : Mem} (hp : Pre tsH tsG s) (hf : Frame (vwrR s) s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 6) (stackArg s 7).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega_arith)
      (by have := hp.preWrap; have := List.mem_range.mp hi; omega_arith)
  · intro r hr
    simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.preStack
    · exact hp.preScr

theorem call_pre {s t : State} (hp : Pre tsH tsG s) (hsp : t.gpr .rsp = fb s)
    (hargs : ∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) (hdi : t.gpr .rdi = stackArg s 4)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 6) (hcx : t.gpr .rcx = stackArg s 7)
    (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    pdChkContract.pre (t.callEntry.withRegions (callRd s) (cWr s)) := by
  have hE : ∀ i < 4, stackArg (t.callEntry.withRegions (callRd s) (cWr s)) i = vArg s i :=
    fun i hi => (vstackArg_call hp.toVPre hsp _ _ hi).trans (hargs i hi)
  simp only [pdChkContract, pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hsp, stackArgAddr_call hsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), vArg]
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have h8' := vfb_sub8 hp.toVPre
  have hsc := vsc_sub hp.toVPre
  have toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  have hsg : (⟨stackArg s 0, (s.gpr .rsi).toNat⟩ : Region) = ⟨stackArg s 0, (stackArg s 1).toNat⟩ := by rw [hp.hsg]
  have dsgs : (⟨stackArg s 0, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ := by
    rw [hsg]; exact hp.dsgs
  have dKsg : (vstkR s).Disjoint ⟨stackArg s 0, (s.gpr .rsi).toNat⟩ := by rw [hsg]; exact hp.dKsg
  have wSg : (stackArg s 0).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by have := hp.wSg; have := hp.hsg; omega_arith
  -- What lies in what.
  have sI : Region.Sub ⟨stackArg s 4, (s.gpr .rsi).toNat⟩ ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ :=
    Region.sub_prefix (by omega_arith)
  have sR : Region.Sub ⟨off (stackArg s 4) oRsa, (stackArg s 5 - 1024#64).toNat * 8⟩
      ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ := Offset.sub_base _ (by rw [hsc]; omega_arith)
  have sA : Region.Sub ⟨fb s, 32⟩ (vstkR s) := fun a h => vframe_sub s a (Region.sub_prefix (by decide) a h)
  have sRet : Region.Sub ⟨fb s - 8, 8⟩ (vstkR s) := vret8_sub s
  have dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega_arith)).symm
  have dIR : (⟨stackArg s 4, (s.gpr .rsi).toNat⟩ : Region).Disjoint
      ⟨off (stackArg s 4) oRsa, (stackArg s 5 - 1024#64).toNat * 8⟩ :=
    Offset.base_disjoint _ (by omega_arith) (by rw [hsc]; omega_arith)
  have hsA : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by omega_arith, rfl, rfl, (hp.preScr.sub_right sI).symm, (hp.des.sub_right sI).symm, (dsgs.sub_right sI).symm,
    dIR, hsA.sub_left sI,
    hp.preScr.sub_right sR, hp.des.sub_right sR, dsgs.sub_right sR, hsA.sub_left sR,
    (hp.dKs.sub_left sRet).sub_right sI, hp.preStack.symm.sub_left sRet, hp.dKe.sub_left sRet, dKsg.sub_left sRet,
    (hp.dKs.sub_left sRet).sub_right sR, dRA,
    by omega_arith, hp.preWrap, hp.wE, wSg, by rw [toNat_off (by omega_arith), hsc]; omega_arith,
    ⟨hk1, hk2⟩, hp.preLen, trivial, hp.L1, hp.L2, by unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; rw [hsc]; omega_arith⟩

theorem call_covers {s t : State} (hp : Pre tsH tsG s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr) :
    Covers (callRd s ++ cWr s) (t.rd ++ t.wr) ∧ Covers (cWr s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hk1 := hp.k1
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsc := vsc_sub hp.toVPre
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (cWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [cWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hscr, 0, (BitVec.add_zero _).symm, by dsimp only; omega_arith⟩
    · exact ⟨_, hscr, oRsa, rfl, by dsimp only; rw [hsc]; omega_arith⟩
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩,
      ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArgAddr s 0, 80⟩]
      (t.rd ++ t.wr) := by rw [hrd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hrd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · rw [← hp.hsg]
    exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩

theorem call_ok (v : PublicImpl)
    {s t : State} (hp : Pre tsH tsG s) (hst : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    (hM : Frame (vwrR s) s.mem t.mem)
    (hargs : ∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) (hdi : t.gpr .rdi = stackArg s 4)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 6) (hcx : t.gpr .rcx = stackArg s 7)
    (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (vwrR s) s.mem t'.mem ∧
      (∀ x, ((frR s).Contains x 1 ∨ ((⟨stackArg s 4, oRsa⟩ : Region).Contains x 1 ∧
        ¬ (⟨stackArg s 4, (s.gpr .rsi).toNat⟩ : Region).Contains x 1)) → t'.mem x = t.mem x) ∧
      (validCache s → Spec.Rsa.written t'.mem (stackArg s 4) (s.gpr .rsi).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat))) := by
  obtain ⟨hc, hw⟩ := call_covers hp hrd hwr
  have hpre := Pc.call_pre hp hst hargs hdi hsi hdx hcx h8 h9
  have hd : v.code.x86_64Depth = 0 := x86_64Depth_zero v.nosp v.depth
  refine X86_64.WP.callF (s := t) (k := pdChkContract) v.ok (SpSafe.of_all v.spSafe) (by omega_arith) hpre hc hw ?_
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  have c2 : oRsa = 8192 := rfl
  have c1 : oEm = 2560 := rfl
  have hsc := vsc_sub hp.toVPre
  rw [hst, hd] at hf
  have sEm : Region.Sub ⟨stackArg s 4, (s.gpr .rsi).toNat⟩ (vscrR s) := Region.sub_prefix (by omega_arith)
  have sScr : Region.Sub ⟨off (stackArg s 4) oRsa, (stackArg s 5 - 1024#64).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega_arith)
  have sBel : Region.Sub (below (fb s) (0 + 8)) (vstkR s) := vret8_sub s
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), fun x hx => hf x fun r hr hc => ?_, ?_⟩
  · simp only [cWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sEm⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sScr⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · simp only [cWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have dFb : (frR s).Disjoint (below (fb s) (0 + 8)) := Offset.base_disjoint_below (fb s) (by omega_arith)
    rcases hx with hx | ⟨hx, hnx⟩ <;> rcases hr with rfl | rfl | rfl
    · exact (hp.dKs.sub_left (vframe_sub s)) x hx (sEm x hc)
    · exact (hp.dKs.sub_left (vframe_sub s)) x hx (sScr x hc)
    · exact dFb x hx hc
    · exact hnx hc
    · exact (Offset.base_disjoint (stackArg s 4) (e := oRsa) (n := (stackArg s 5 - 1024#64).toNat * 8)
        (k := oRsa) (Nat.le_refl _) (by rw [hsc]; omega_arith)) x hx hc
    · exact ((hp.dKs.sub_left sBel).symm.sub_left (Region.sub_prefix (by omega_arith))) x hx hc
  · have hE : ∀ i < 4, stackArg (t.callEntry.withRegions (callRd s) (cWr s)) i = vArg s i :=
      fun i hi => (vstackArg_call hp.toVPre hst _ _ hi).trans (hargs i hi)
    have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
    have b : ∀ {R : Region}, (vstkR s).Disjoint R → R.Disjoint (vscrR s) → R.len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
      fun hK hS hl => bytesAt_frame fSE (vin_apart hK hS) hl
    simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      hdi, hsi, hdx, hcx, h8, h9, hE 0 (by decide), vArg, hm₂, hg₂ .rax (by decide)] at hpost
    rw [pre_words hp fSE,
      b (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hp.dKe hp.des (by have := hp.wE; dsimp only; omega_arith),
      b (R := ⟨stackArg s 0, (s.gpr .rsi).toNat⟩) (by rw [← hp.hsg]; exact hp.dKsg) (by rw [← hp.hsg]; exact hp.dsgs)
        (by have := hp.wSg; have := hp.hsg; dsimp only; omega_arith)] at hpost
    exact fun hcache => hpost _ (bytesAt_length ..) hcache


end VG.Proof.RsaPss.X86_64.Pc

end

end

/-! ### `RsaPss.X86_64.PcCArgs`, which only this module used -/

section

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: the public-key operation's arguments

`pubArgsC_ok`: its output at the start of `scratch`, the signature, the
cache, and the rest of `scratch` after our part.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {tsH tsG : List FnTable}

def pubA1 : List Instr :=
  ([.mov .rax (.mem (sp sSig)), .store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] : List Instr) ++
  scr .rax oRsa ++ ([.store (sp 16) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 24) .rax, .mov .rdi (.mem (sp sScr)), .mov .rsi (.mem (sp sK))] : List Instr)

theorem pubArgsC_eq : pubArgsC = pubA1 ++ ([.mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7))] : List Instr) ++
    ([.mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))] : List Instr) := rfl

theorem pubA1_ok {s : State} {u : State} (L : Lay u (fb s) (stackArg s 4))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 4) V W)
    (h17 : W 17 = s.gpr .rsi) (h22 : W 22 = stackArg s 5) (h38 : W 38 = stackArg s 0) :
    WP isa (.block pubA1) u fun u' => Keep [.rax, .rdi, .rsi] u u' ∧
      Lay u' (fb s) (stackArg s 4) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 4) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧ (∀ i < nW, 4 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = stackArg s 4 ∧ u'.gpr .rsi = s.gpr .rsi := by
  have G' := L.geo
  have hs : u.mem.readW (off (fb s) sScr) 64 = stackArg s 4 := L.slot
  set S := stackArg s 4
  obtain Ra := R.wf G' (k := 0) (by decide) (stackArg s 0)
  obtain Rb := Ra.wf G' (k := 1) (by decide) (s.gpr .rsi)
  obtain Rc := Rb.wf G' (k := 2) (by decide) (off S oRsa)
  obtain Rd := Rc.wf G' (k := 3) (by decide) (stackArg s 5 - BitVec.ofNat 64 1024)
  simp only [Nat.reduceMul, off_zero] at Ra Rb Rc Rd
  obtain hst0 : InRegions u.wr (fb s) 8 := by simpa only [off_zero] using L.st (d := 0) (by decide)
  obtain f0 : u.mem.readW (off (fb s) sSig) 64 = stackArg s 0 := by
    rw [R.rd (d := sSig) 38 rfl (by decide), h38]
  obtain f1 : (u.mem.writeW (fb s) (stackArg s 0)).readW (off (fb s) sK) 64 = s.gpr .rsi := by
    rw [Ra.rd (d := sK) 17 rfl (by decide)]; simp [upd, h17]
  obtain f2 : ((u.mem.writeW (fb s) (stackArg s 0)).writeW (off (fb s) 8) (s.gpr .rsi)).readW
      (off (fb s) sScr) 64 = S := by
    rw [Rb.rd (d := sScr) 21 rfl (by decide)]; simp only [upd, Nat.reduceEqDiff, ite_false]
    exact (R.rd (d := sScr) 21 rfl (by decide)).symm.trans hs
  obtain f3 : (((u.mem.writeW (fb s) (stackArg s 0)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
      (off (fb s) 16) (off S oRsa)).readW (off (fb s) sScrLen) 64 = stackArg s 5 := by
    rw [Rc.rd (d := sScrLen) 22 rfl (by decide)]; simp [upd, h22]
  set m4 := ((((u.mem.writeW (fb s) (stackArg s 0)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
      (off (fb s) 16) (off S oRsa)).writeW (off (fb s) 24) (stackArg s 5 - BitVec.ofNat 64 1024)) with hm4
  obtain g : ∀ k, 4 ≤ k → k < nW → m4.readW (off (fb s) (8 * k)) 64 = W k := fun k hk hk' => by
    refine (Rd.fr k hk').trans ?_; simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  obtain g21 : m4.readW (off (fb s) sScr) 64 = S :=
    (g 21 (by decide) (by decide)).trans ((R.rd (d := sScr) 21 rfl (by decide)).symm.trans hs)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi] (Q := fun u' => u'.mem = m4 ∧
      u'.gpr .rdi = S ∧ u'.gpr .rsi = s.gpr .rsi) ?_ rfl) fun u2 ⟨⟨hm, h1, h2⟩, k2⟩ => ?_
  · xrun [pubA1, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sSig) (by decide), f0,
      L.ld (d := sScr) (by decide), hst0,
      L.st (d := 8) (by decide), L.st (d := 16) (by decide), L.st (d := 24) (by decide),
      L.ld (d := sK) (by decide), L.ld (d := sScrLen) (by decide), f1, f2, f3, g21,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 < 2 ^ 31 by decide),
      show m4.readW (off (fb s) sK) 64 = s.gpr .rsi from (g 17 (by decide) (by decide)).trans h17,
      show S + BitVec.ofNat 64 oRsa = off S oRsa from rfl]
    rw [show BitVec.signExtend 64 (1024 : BitVec 32) = BitVec.ofNat 64 1024 by decide] at *
    rw [← hm4, g21]
    exact ⟨rfl, rfl, (g 17 (by decide) (by decide)).trans h17⟩
  obtain R2 : Rep u2.mem (fb s) S V _ := hm ▸ Rd
  refine ⟨k2, L.of_rep' R R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2,
    ⟨_, R2, fun i hi => ?_, fun i hi h4 => ?_⟩, h1, h2⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with h | h | h | h <;> subst h
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]; rfl
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]

theorem pubArgsC_ok {s u : State} (hp : Pre tsH tsG s) (L : Lay u (fb s) (stackArg s 4))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 4) V W)
    (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem)
    (h17 : W 17 = s.gpr .rsi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 5) (h38 : W 38 = stackArg s 0) :
    WP isa (.block pubArgsC) u fun u' =>
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧ Lay u' (fb s) (stackArg s 4) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 4) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧ (∀ i < nW, 4 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = stackArg s 4 ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = stackArg s 6 ∧
      u'.gpr .rcx = stackArg s 7 ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx := by
  refine WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] ?_ (by decide) |>
    WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  rw [pubArgsC_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (pubA1_ok L R h17 h22 h38)) fun t ⟨⟨k, L1, ⟨W1, R1, ha, hb⟩, hdi, hsi⟩, f⟩ => ?_
  obtain hf := vframe_keep hp.toVPre hw L.rsp hM f
  refine WP.mono (load_pre hp L1.rsp (k.2.1.trans hrd) hf) fun v ⟨k2, hm, hdx, hcx⟩ => ?_
  obtain L2 : Lay v (fb s) (stackArg s 4) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm])
  obtain R2 : Rep v.mem (fb s) (stackArg s 4) V W1 := hm ▸ R1
  refine WP.mono (WP.keep [.r8, .r9] (Q := fun y => y.mem = v.mem ∧ y.gpr .r8 = s.gpr .rdx ∧
    y.gpr .r9 = s.gpr .rcx) ?_ rfl) fun y ⟨⟨hm3, h8, h9⟩, k3⟩ => ?_
  · xrun [ea_sp, L2.rsp, L2.ld (d := sE) (by decide), L2.ld (d := sEl) (by decide),
      R2.rd (d := sE) 19 rfl (by decide), R2.rd (d := sEl) 20 rfl (by decide),
      hb 19 (by decide) (by decide), hb 20 (by decide) (by decide), h19, h20]
  refine ⟨L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), ⟨W1, hm3 ▸ R2, ha, hb⟩,
    (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans hdi),
    (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans hsi), (k3.gpr (by decide)).trans hdx,
    (k3.gpr (by decide)).trans hcx, h8, h9⟩

end VG.Proof.RsaPss.X86_64.Pc

end

end


/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: correctness

`codeC_ok`: from the entry state, `verifyC` refuses a modulus whose first
byte is zero, computes `emBits`, calls the public-key operation for its
output at the start of `scratch`, and `checkEncoding` for the hash function
of the table `hash` (by its index, `byIdx`) on its last `emLen` bytes, and
returns 1 exactly when those are a consistent encoding and the bytes before
them zero, which, when the cache matches the modulus, is `RsaPss.verify`
(`verify_encode₂`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)

variable {tsH tsG : List FnTable}

/-- Before the epilogue: the result in `rax` if the cache matches, the saved
registers in their slots. -/
structure CDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 4)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 8) = some H →
    Spec.MdHashTable.hashAt 64 s.mem (stackArg s 9) = some G → validCache s →
    (t.gpr .rax).setWidth 32 = if verifyOut H G s then 1 else 0

theorem restoreC_ok {s t : State} (D : CDone s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      ∀ m u, Frame [⟨fb s, frameBytes⟩] t'.mem m →
        (∀ r ∈ calleeSaved, ({ freedF t' with mem := m, unknowns := u } : State).gpr r = s.gpr r) ∧ (verifyK tsH tsG).post s ({ freedF t' with mem := m, unknowns := u } : State) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  obtain hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun _ _ _ => ⟨fun r hr => ?_, ?_⟩⟩
  · show (freedF t').gpr r = s.gpr r
    simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · intro H G a b hc
    show (t'.gpr .rax).setWidth 32 = _
    rw [k.gpr (show Reg.rax ∉ [Reg.rbx, .rbp, .r12] by decide)]
    exact D.out H G a b hc

/-- What verification needs of the tables in the entry state `s`: the
index `i` of the hash function of `hash`, the functions `T` of both tables,
the hash functions `Hs` and `Gs` they name, and that `checkEncoding` for the
index `i` checks the encoding with them. -/
structure KSel (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) (s : State) (i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) : Prop where
  mem : i ∈ idxs
  idx : s.mem.readW (off (stackArg s 8) 40) 64 = BitVec.ofNat 64 i
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 8) (stackArg s 9) s
  hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 8) = some Hs
  hG : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 9) = some Gs
  hD : T.H.D = (s.gpr .r9).toNat
  ok : ∀ s', (chkK T Hs Gs).pre s' → ∃ t s'', Exec isa (checkEncoding f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (chkK T Hs Gs).post s' s''

/-- The table `hash` to `r11`, the flags kept. -/
theorem vr11Arg_ok {s u : State} (hp : Pre tsH tsG s) (hsp : u.gpr .rsp = fb s) (hrd : u.rd = s.rd)
    (hM : Frame (vwrR s) s.mem u.mem) :
    WP isa (.block [.mov .r11 (.mem (arg 8))]) u fun u' => Keep [.r11] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r11 = stackArg s 8 ∧ u'.zf = u.zf := by
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = stackArg s 8 ∧ u'.zf = u.zf) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [arg, ea_sp, hsp, arg_read hp hrd (show 8 < 10 by decide), arg_keep hp hM (show 8 < 10 by decide)]

/-- The index of the table `hash`'s hash function to its slot, the flags
kept. -/
theorem vidxSlot_ok {s u : State} (hp : Pre tsH tsG s) (L : Lay u (fb s) (stackArg s 4)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 4) V W) (hrd : u.rd = s.rd)
    (hM : Frame (vwrR s) s.mem u.mem) (h11 : u.gpr .r11 = stackArg s 8) :
    WP isa (.block idxSlot) u fun u' => Lay u' (fb s) (stackArg s 4) ∧ Keep [.r11] u u' ∧
      Rep u'.mem (fb s) (stackArg s 4) V (upd W 47 (s.mem.readW (off (stackArg s 8) 40) 64)) ∧ u'.zf = u.zf ∧
      Frame (vwrR s) s.mem u'.mem := by
  have hw := hp.wTH
  have G' := L.geo
  obtain hin : InRegions (u.rd ++ u.wr) (off (stackArg s 8) 40) 8 :=
    ⟨⟨stackArg s 8, 88⟩, List.mem_append_left _ (by rw [hrd, hp.hrdE]; simp),
      Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  obtain R1 := R.wf G' (k := 47) (by decide) (s.mem.readW (off (stackArg s 8) 40) 64)
  rw [show off (fb s) (8 * 47) = off (fb s) sIdx from rfl] at R1
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) sIdx)
      (s.mem.readW (off (stackArg s 8) 40) 64) ∧ u'.zf = u.zf) ?_ rfl) fun u' ⟨⟨hm, hz⟩, k⟩ => ?_
  · xrun [idxSlot, ea_at, ea_sp, L.rsp, h11, hin, vidx_read hp hM, L.st (d := sIdx) (by decide)]
  obtain R' := hm ▸ R1
  refine ⟨L.of_rep' R R' (by simp [upd]) (k.gpr (by decide)) k.2.2, k, R', hz, ?_⟩
  rw [hm]; exact vframe_w hp hM (by decide) _

/-- The index to `r11`. -/
theorem vidxLoad_ok {s u : State} (L : Lay u (fb s) (stackArg s 4)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem (fb s) (stackArg s 4) V W) :
    WP isa (.block idxLoad) u fun u' => Keep [.r11] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r11 = W 47 := by
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = W 47) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [idxLoad, ea_sp, L.rsp, L.ld (d := sIdx) (by decide), R.rd (d := sIdx) 47 rfl (by decide)]

theorem written_getD {m : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (h : Spec.Rsa.written m out n r o) : Spec.Rsa.bytesAt m out n = o.getD (Spec.RsaPss.zeros n) := by
  cases o with
  | none => exact h.2
  | some x => exact h.2

/-- The result: the check's, if the first `lo` bytes are zero. -/
theorem acc_out {lo : Nat} (hlo : lo ≤ 1) {x : List Byte} (hx : 1 ≤ x.length) {ve : Bool} {r : BitVec 64}
    (hr : r.setWidth 32 = if ve then 1 else 0) :
    (r &&& accV lo (x.getD 0 0)).setWidth 32 =
      if (x.take lo == Spec.RsaPss.zeros lo && ve) then 1 else 0 := by
  rw [BitVec.setWidth_and, hr]
  obtain ⟨a, t, rfl⟩ : ∃ a t, x = a :: t := by
    cases x with
    | nil => simp at hx
    | cons a t => exact ⟨a, t, rfl⟩
  rcases (show lo = 0 ∨ lo = 1 by omega_using [hlo]) with rfl | rfl
  · cases ve <;> simp [accV, Spec.RsaPss.zeros]
  · by_cases ha : a = 0
    · subst ha; cases ve <;> simp [accV, Spec.RsaPss.zeros]
    · have ha' : (a = 0#8) ↔ False := ⟨ha, False.elim⟩
      cases ve <;> simp [accV, Spec.RsaPss.zeros, ha']

/-- The slots after `emBitsB`. -/
def vW (W : Nat → BitVec 64) (s : State) (eb : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 27 (BitVec.ofNat 64 eb)) 28 (BitVec.ofNat 64 (Spec.RsaPss.emLength eb))) 26
    (BitVec.ofNat 64 ((s.gpr .rsi).toNat - Spec.RsaPss.emLength eb))

/-- `emBits`, then the public-key operation's arguments. -/
theorem vprep_ok {s u : State} (hp : Pre tsH tsG s) (L : Lay u (fb s) (stackArg s 4)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 4) V W) (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd)
    (hM : Frame (vwrR s) s.mem u.mem) (h17 : W 17 = s.gpr .rsi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 5) (h38 : W 38 = stackArg s 0) {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block (emBitsB ++ pubArgsC)) u fun u' => Lay u' (fb s) (stackArg s 4) ∧
      Keep [.rdx, .rax, .r8, .rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 4) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧
        (∀ i < nW, 4 ≤ i → W' i = vW W s (ebV (s.gpr .rsi).toNat x) i)) ∧
      u'.gpr .rdi = stackArg s 4 ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = stackArg s 6 ∧
      u'.gpr .rcx = stackArg s 7 ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx ∧
      Frame (vwrR s) s.mem u'.mem := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16) (emBitsB_ok L R (k := (s.gpr .rsi).toNat)
    (x := x) (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk1]) hk2 hx h0 hax)) fun t ⟨⟨L3, k3, R3⟩, f3⟩ => ?_
  obtain hM3 := vframe_keep hp.toVPre hw L.rsp hM f3
  exact WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16) (pubArgsC_ok hp L3 R3 (k3.2.2.trans hw)
    (k3.2.1.trans hrd) hM3 (by simp [upd, h17]) (by simp [upd, h19]) (by simp [upd, h20])
    (by simp [upd, h22]) (by simp [upd, h38])))
    fun t' ⟨⟨k4, L4, hW, a, b, c, d, e, f⟩, f4⟩ =>
      ⟨L4, k3.trans k4, hW, a, b, c, d, e, f, vframe_keep hp.toVPre (k3.2.2.trans hw) L3.rsp hM3 f4⟩

/-- The slots after `idxSlot`. -/
def vproW1 (s : State) : Nat → BitVec 64 := upd (vproW s) 47 (s.mem.readW (off (stackArg s 8) 40) 64)

theorem codeC_ok {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns}
    (hspK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl)
    {s : State} (h : (verifyK tsH tsG).pre s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : KSel f g s i T Hs Gs) :
    WP isa (Impl.RsaPss.X86_64.verifyC f g v.name v.code) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (verifyK tsH tsG).post s s' ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  obtain hp := pre_of h
  obtain hF := vfb_toNat hp.toVPre
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hHl : Hs.len = T.H.D := ((hp.hdl Hs E.hH).symm.trans E.hD.symm)
  obtain hHs : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 8) = some H →
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 9) = some G → H = Hs ∧ G = Gs := fun H G a b =>
    ⟨Option.some.inj (a.symm.trans E.hH), Option.some.inj (b.symm.trans E.hG)⟩
  refine wp_frame (by have := hp.sp1; unfold verifyStack chkStack frameBytes at *; omega_arith) ?_
  rw [verifyCBody]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono_mxs (by decide) (verifyPro_ok hp.toVPre) fun t1 ⟨k1, L1, R1, f1⟩ sy1 hmx1 => ?_
  obtain hM1 : Frame (vwrR s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine WP.mono_mxs (by decide) (vn0_ok hp.toVPre L1 R1 (by simp [vproW, upd]) k1.2.1 hM1)
    fun t2 ⟨k2, hm2, hax2, hz2⟩ sy2 hmx2 => ?_
  obtain L2 : Lay t2 (fb s) (stackArg s 4) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  obtain hM2 : Frame (vwrR s) s.mem t2.mem := hm2 ▸ hM1
  refine WP.mono_mxs (by decide) (vr11Arg_ok hp L2.rsp (k2.2.1.trans k1.2.1) hM2)
    fun t2' ⟨k2', hm2', h11, hz2'⟩ sy2' hmx2' => ?_
  obtain L2' : Lay t2' (fb s) (stackArg s 4) := L2.congr (k2'.gpr (by decide)) k2'.2.2 (by rw [hm2'])
  refine WP.seq (WP.mono_mxs (by decide) (vidxSlot_ok hp L2' (hm2' ▸ hm2 ▸ R1)
      (k2'.2.1.trans (k2.2.1.trans k1.2.1)) (hm2' ▸ hM2) h11)
    fun t3 ⟨L3, k3, R3, hz3, hM3⟩ sy3 hmx3 => ?_)
  obtain hw3 : t3.wr = frR s :: s.wr := k3.2.2.trans (k2'.2.2.trans (k2.2.2.trans k1.2.2))
  obtain hrd3 : t3.rd = s.rd := k3.2.1.trans (k2'.2.1.trans (k2.2.1.trans k1.2.1))
  obtain hsy3 : t3.syms = s.syms := sy3.trans (sy2'.trans (sy2.trans sy1))
  obtain e3 : t3.mxcsr = s.mxcsr := hmx3.trans (hmx2'.trans (hmx2.trans hmx1))
  obtain hcs3 : ∀ r ∈ [Reg.r13, .r14, .r15], t3.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.r11] ∧ r ∉ [Reg.rsi, .rax] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k3.gpr this.1, k2'.gpr this.1, k2.gpr this.2, k1.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  obtain hax3 : t3.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), hax2]
  refine WP.seq (WP.mono (Q := fun (t3 : State) => CDone s t3 ∧
      t3.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) ?_
    fun t3 ⟨D, hm⟩ => WP.mono_mx (by decide) (restoreC_ok D) fun t' ⟨a, b, c⟩ hm' =>
      ⟨a, b, fun m u fm => ⟨(c m u fm).1, (c m u fm).2,
        by rw [show ({ freedF t' with mem := m, unknowns := u } : State).mxcsr = t'.mxcsr from rfl, hm']
           exact hm⟩⟩)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdi) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdi + 1) ((s.gpr .rsi).toNat - 1) with hrest
  obtain hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega_arith)
  obtain hrl : rest.length = (s.gpr .rsi).toNat - 1 := by simp [hrest, Spec.Rsa.bytesAt]
  refine WP.ite (M := isa) _ (show isa.eval .e t3 = _ by rw [show isa.eval .e t3 = t3.zf from rfl, hz3, hz2', hz2])
    (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    obtain h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    obtain hf : verifyOut Hs Gs s = false := by rw [verifyOut, hnB, h0]; exact RsaPss.verify_zero₂ ..
    refine WP.mono_mx (by decide) (vfail_done L3 R3 hw3 hcs3 (by simp [vproW, upd]) (by simp [vproW, upd])
      (by simp [vproW, upd]) hf) fun _ D hm' => ⟨⟨D.L, D.wr, D.cs, D.rbx, D.rbp, D.r12, fun H G a b _ => ?_⟩,
        by rw [hm', e3]⟩
    obtain ⟨rfl, rfl⟩ := hHs H G a b
    exact D.out
  rw [decide_eq_false_iff_not] at hb
  obtain h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  obtain hl8 := RsaPss.log2_lt8 n₀
  set k := (s.gpr .rsi).toNat with hk
  set eb := ebV k n₀.toNat with heb_def
  set el := Spec.RsaPss.emLength eb with hel_def
  set lo := k - el with hlo_def
  obtain hlo : lo ≤ 1 := lo_le hl8 (by omega_arith)
  obtain heb : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)) - 1 = eb := by
    rw [hnB, RsaPss.emBits_eq rest h0, hrl]; rfl
  obtain heb1 : 1 ≤ eb := by rw [heb_def]; unfold ebV; omega_arith
  obtain heb2 : eb ≤ Proof.RsaPss.maxEmBits := by
    rw [heb_def]; unfold ebV Proof.RsaPss.maxEmBits; omega_arith
  obtain hlok : lo + el = k := by
    rw [hlo_def, hel_def, heb_def]; unfold Spec.RsaPss.emLength ebV; omega_arith
  -- `emBits` and the public-key operation's arguments.
  refine WP.seq (WP.mono_mxs (by decide) (vprep_ok hp L3 R3 hw3 hrd3 hM3 (by simp [vproW, upd])
    (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) n₀.isLt hb hax3)
    fun t4 ⟨L4, k4, ⟨W4, R4, hW4a, hW4b⟩, hdi4, hsi4, hdx4, hcx4, h84, h94, hM4⟩ sy4 hmx4 => ?_)
  obtain hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans hw3
  obtain hrd4 : t4.rd = s.rd := k4.2.1.trans hrd3
  obtain g4 : ∀ j, j < nW → 4 ≤ j → j ≠ 26 → j ≠ 27 → j ≠ 28 → W4 j = vproW1 s j := fun j hj h4 a b c => by
    rw [hW4b j hj h4]; simp only [vW, upd, vproW1]; rw [ifn a, ifn c, ifn b]
  -- The public-key operation.
  refine WP.seq (X86_64.WP.mono_syms (call_ok v hp L4.rsp hrd4 hw4 hM4
    (fun i hi => (R4.fr i (by unfold nW frameBytes; omega_arith)).trans (hW4a i hi)) hdi4 hsi4 hdx4 hcx4 h84 h94)
    fun t5 ⟨rd5, wr5, cs5, mx5, hM5, hk5, hout5⟩ sy5 => ?_)
  obtain R5 := R4.of_call L4.geo (m' := t5.mem) (rgs := [(0, k)]) (fun x hx hin => hk5 x (by
      rcases hin with hin | hin
      · refine .inr ⟨hin, ?_⟩
        have := hx _ (List.mem_singleton_self _)
        rwa [off_zero] at this
      · exact .inl hin)) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'; dsimp only; unfold oRsa; omega_arith)
  set V5 := fun o => if inR [(0, k)] o then t5.mem (off (stackArg s 4) o)
    else (fun o => s.mem (off (stackArg s 4) o)) o with hV5
  obtain L5 : Lay t5 (fb s) (stackArg s 4) := L4.of_rep' R4 R5 rfl (cs5 .rsp (by decide)) wr5
  -- `sAcc`, `checkEncoding`'s arguments, and the index.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mxs (by decide) (chkArgs_ok hp L5 R5 (wr5.trans hw4) (rd5.trans hrd4) hM5
    (lo := lo) (el := el) (eb := eb)
    ((g4 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [vproW1, vproW, upd]))
    ((g4 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [vproW1, vproW, upd]))
    (by rw [hW4b 26 (by decide) (by decide)]; simp only [vW, upd, ↓reduceIte]; try rfl)
    (by rw [hW4b 27 (by decide) (by decide)]; simp only [vW, upd, Nat.reduceEqDiff, ↓reduceIte]; try rfl)
    (by rw [hW4b 28 (by decide) (by decide)]; simp only [vW, upd, Nat.reduceEqDiff, ↓reduceIte]; try rfl)
    ((g4 37 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [vproW1, vproW, upd])) hlo)
    fun t6 ⟨L6, k6, R6, hM6, hdi6, hsi6, hdx6, hcx6, h86, h96⟩ sy6 hmx6 => ?_
  refine WP.mono_mxs (by decide) (vidxLoad_ok L6 R6) fun t6' ⟨k6', hm6', h116⟩ sy6' hmx6' => ?_
  obtain hi11 : t6'.gpr .r11 = BitVec.ofNat 64 i := by
    rw [h116, ← E.idx]; simp only [chkW, upd]
    rw [ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide),
      g4 47 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [vproW1, upd]
  obtain R6' := hm6' ▸ R6
  obtain L6' : Lay t6' (fb s) (stackArg s 4) := L6.congr (k6'.gpr (by decide)) k6'.2.2 (by rw [hm6'])
  -- The index chooses `checkEncoding`.
  refine WP.seq (byIdx_wp (i := i) E.mem cmpOk_idxs hi11 fun t7 k7 hm7 sy7 hx7 => ?_)
  obtain R7 := hm7 ▸ R6'
  obtain g7 : ∀ r, r ≠ .r11 → t7.gpr r = t6.gpr r := fun r hr =>
    (k7.gpr (List.not_mem_nil)).trans (k6'.gpr (by simpa using hr))
  obtain KA : KAt T s t7 lo eb el :=
    { sp := (k7.gpr (List.not_mem_nil)).trans L6'.rsp, rd := k7.2.1.trans (k6'.2.1.trans (k6.2.1.trans (rd5.trans hrd4))),
      wr := k7.2.2.trans (k6'.2.2.trans (k6.2.2.trans (wr5.trans hw4))), M := hm7 ▸ hm6' ▸ hM6,
      sy := sy7.trans (sy6'.trans (sy6.trans (sy5.trans (sy4.trans hsy3)))),
      w0 := (R7.fr 0 (by decide)).trans (by simp [chkW, upd]), w1 := (R7.fr 1 (by decide)).trans (by simp [chkW, upd]),
      w2 := (R7.fr 2 (by decide)).trans (by simp [chkW, upd]), w3 := (R7.fr 3 (by decide)).trans (by simp [chkW, upd]),
      di := (g7 _ (by decide)).trans hdi6, si := (g7 _ (by decide)).trans hsi6, dx := (g7 _ (by decide)).trans hdx6,
      cx := (g7 _ (by decide)).trans hcx6, r8 := (g7 _ (by decide)).trans h86, r9 := (g7 _ (by decide)).trans h96,
      hlo := by omega_arith, eb1 := heb1, eb2 := heb2, hel := rfl, hD := E.hD, tabs := E.tabs }
  -- `checkEncoding`.
  refine WP.mono (ck_call (Hs := Hs) (Gs := Gs) E.ok (hspK i E.mem) (hdK i E.mem) hp KA R7)
    fun t8 ⟨rd8, wr8, cs8, mx8, hM8, sy8, R8, hax8⟩ => ?_
  obtain L8 : Lay t8 (fb s) (stackArg s 4) := (L6'.congr (k7.gpr (List.not_mem_nil)) k7.2.2 (by rw [hm7])).of_rep'
    R7 R8 rfl (cs8 .rsp (by decide)) wr8
  -- The result, if the first `lo` bytes are zero.
  refine WP.mono_mx (by decide) (WP.keep [.rax] (Q := fun y => y.mem = t8.mem ∧
      y.gpr .rax = t8.gpr .rax &&& accV lo (V5 0)) ?_ rfl) fun y ⟨⟨hm9, hax9⟩, k9⟩ hmx9 => ?_
  · xrun [ea_sp, L8.rsp, L8.ld (d := sAcc) (by decide), R8.rd (d := sAcc) 33 rfl (by decide)]
    simp [chkW, upd]
  obtain R9 := hm9 ▸ R8
  obtain w : ∀ j, 40 < j → j < nW → j ≠ 47 → chkW W4 s lo (V5 0) j = vproW s j := fun j hj hj' h47 => by
    simp only [chkW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith),
      ifn (by omega_arith)]
    rw [g4 j hj' (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
    simp only [vproW1, upd]; rw [ifn h47]
  refine ⟨⟨L8.congr (k9.gpr (by decide)) k9.2.2 (by rw [hm9]), k9.2.2.trans (wr8.trans (k7.2.2.trans
      (k6'.2.2.trans (k6.2.2.trans (wr5.trans hw4))))), fun r hr => ?_, ?_, ?_, ?_, fun H G a b hc => ?_⟩, ?_⟩
  · have h1 : r ∈ calleeSaved := by simp at hr; rcases hr with rfl | rfl | rfl <;> decide
    rw [k9.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), cs8 r h1,
      g7 r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), cs5 r h1,
      k4.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs3 r hr]
  · rw [R9.rd (d := sRbx) 41 rfl (by decide), w 41 (by decide) (by decide) (by decide)]; simp [vproW, upd]
  · rw [R9.rd (d := sRbp) 42 rfl (by decide), w 42 (by decide) (by decide) (by decide)]; simp [vproW, upd]
  · rw [R9.rd (d := sR12) 43 rfl (by decide), w 43 (by decide) (by decide) (by decide)]; simp [vproW, upd]
  · obtain ⟨rfl, rfl⟩ := hHs H G a b
    obtain hbx := written_getD (hout5 hc)
    set x := (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 0) k)).getD
        (Spec.RsaPss.zeros k) with hx
    obtain hxl : x.length = k := by rw [← hbx, bytesAt_length]
    obtain hin : ∀ o, o < k → inR [(0, k)] o := fun o ho =>
      ⟨_, List.mem_singleton_self _, by dsimp only; omega_using [], by dsimp only; omega_using [ho]⟩
    obtain hb0 : V5 0 = x.getD 0 0 := by
      rw [← hbx, hV5]; dsimp only; rw [ifp (hin 0 (by omega_arith))]
      rw [List.getD_eq_getElem?_getD, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega_arith)]
      simp [off]
    obtain hem : Spec.Rsa.bytesAt t7.mem (off (stackArg s 4) lo) el = x.drop lo := by
      rw [← hbx]
      apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega_arith)
      intro i h1 h2
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_drop, off_plus]
      rw [R7.scr _ (by unfold oRsa; omega_arith), hV5]; dsimp only
      rw [ifp (hin _ (by omega_arith))]
    rw [hem, ← hHl] at hax8
    rw [hax9, hb0, acc_out hlo (by omega_arith) hax8, verifyOut,
      RsaPss.verify_encode₂ H G heb (by rw [bytesAt_length, bytesAt_length])
        (by rw [bytesAt_length]; unfold Spec.RsaPss.emLength at *; omega_arith)]
    simp only [bytesAt_length]
    rfl
  · rw [hmx9, mx8, hx7, hmx6', hmx6, mx5, hmx4, e3]

end VG.Proof.RsaPss.X86_64.Pc
