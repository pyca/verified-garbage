module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCtx
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx

import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedArgs
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame

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
  have h0 : u.mem S = V 0 := by have := R.scr 0 (by decide); rwa [off_zero] at this
  have hl0 : InRegions (u.rd ++ u.wr) S 1 := by have := L.sld8 (d := 0) (by decide); rwa [off_zero] at this
  refine WP.mono (WP.keep [.rcx, .r9, .r10, .r11] (Q := fun u' =>
      u'.mem = u.mem.writeW (off F sAcc) (accV lo (V 0)) ∧ u'.gpr .rcx = S ∧ u'.gpr .r10 = BitVec.ofNat 64 lo) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [cA1, ea_sp, ea_at0, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sLo) (by decide),
    L.st (d := sAcc) (by decide), hs, hl0, h0, R.rd (d := sLo) 26 rfl (by decide), h26]
  refine congrArg (u.mem.writeW (off F sAcc)) ?_
  generalize V 0 = b
  rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
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
  have hF := vfb_toNat hp.toVPre
  have := hp.sp2
  exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self (frR s)) v
    (Offset.contains_base _ (by unfold frameBytes at *; omega) (by unfold frameBytes at *; omega))).sub
    fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩)

/-- The tables to `checkEncoding`'s stack arguments 2 and 3. -/
theorem cA4_ok {s u : State} (hp : Pre tsH tsG s) {S : Addr} (L : Lay u (fb s) S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem) :
    WP isa (.block cA4) u fun u' => Lay u' (fb s) S ∧ Keep [.rax] u u' ∧
      Rep u'.mem (fb s) S V (upd (upd W 2 (stackArg s 8)) 3 (stackArg s 9)) ∧ Frame (vwrR s) s.mem u'.mem := by
  have G' := L.geo
  have R1 := R.wf G' (k := 2) (by decide) (stackArg s 8)
  have R2 := R1.wf G' (k := 3) (by decide) (stackArg s 9)
  rw [show off (fb s) (8 * 2) = off (fb s) 16 from rfl] at R1 R2
  rw [show off (fb s) (8 * 3) = off (fb s) 24 from rfl] at R2
  have hM1 := vframe_w hp hM (d := 16) (by decide) (stackArg s 8)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = (u.mem.writeW (off (fb s) 16) (stackArg s 8)).writeW
      (off (fb s) 24) (stackArg s 9)) ?_ rfl) fun u' ⟨hm, k⟩ => ?_
  · xrun [cA4, arg, ea_sp, L.rsp, arg_read hp hrd (show 8 < 10 by decide), arg_read hp hrd (show 9 < 10 by decide),
      arg_keep hp hM (show 8 < 10 by decide), arg_keep hp hM1 (show 9 < 10 by decide),
      L.st (d := 16) (by decide), L.st (d := 24) (by decide)]
  have R' : Rep u'.mem (fb s) S V (upd (upd W 2 (stackArg s 8)) 3 (stackArg s 9)) := by rw [hm]; exact R2
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
  have hk1 := hp.k1; have hk2 := hp.k2
  set S := stackArg s 4
  rw [chkArgs_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16) (cA1_ok L R h26 hlo))
    fun u1 ⟨⟨k1, hm1, hcx1, h101⟩, f1⟩ => ?_
  have hM1 := vframe_keep hp.toVPre hw L.rsp hM f1
  have R1 := R.wf G' (k := 33) (by decide) (accV lo (V 0))
  rw [show off (fb s) (8 * 33) = off (fb s) sAcc from rfl, ← hm1] at R1
  have L1 : Lay u1 (fb s) S := L.of_rep' R R1 (by simp [upd]) (k1.gpr (by decide)) k1.2.2
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .r8, .r9] (Q := fun v => v.mem = u1.mem ∧ v.gpr .rdi = s.gpr .r8 ∧
      v.gpr .rsi = off S lo ∧ v.gpr .rdx = BitVec.ofNat 64 el ∧ v.gpr .r8 = stackArg s 2 ∧ v.gpr .r9 = stackArg s 3)
    ?_ rfl) fun v ⟨⟨hm2, hdi, hsi, hdx, h8, h9⟩, k2⟩ => ?_
  · xrun [cA2, arg, ea_sp, L1.rsp, L1.ld (d := sDig) (by decide), L1.ld (d := sEml) (by decide),
      R1.rd (d := sDig) 37 rfl (by decide), R1.rd (d := sEml) 28 rfl (by decide),
      arg_read hp (k1.2.1.trans hrd) (show 2 < 10 by decide), arg_read hp (k1.2.1.trans hrd) (show 3 < 10 by decide),
      arg_keep hp hM1 (show 2 < 10 by decide), arg_keep hp hM1 (show 3 < 10 by decide), hcx1, h101]
    simp [upd, h37, h28]
  have L2 : Lay v (fb s) S := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep v.mem (fb s) S V (upd W 33 (accV lo (V 0))) := by rw [hm2]; exact R1
  have Ra := R2.wf G' (k := 1) (by decide) (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))
  have Rb := Ra.wf G' (k := 0) (by decide) (off S (8 * kw (s.gpr .rsi).toNat))
  rw [show off (fb s) (8 * 1) = off (fb s) 8 from rfl] at Ra Rb
  rw [show off (fb s) (8 * 0) = fb s from off_zero _] at Rb
  have hst0 : InRegions v.wr (fb s) 8 := by simpa only [off_zero] using L2.st (d := 0) (by decide)
  have hcx2 : v.gpr .rcx = S := by rw [k2.gpr (by decide)]; exact hcx1
  have hM2 : Frame (vwrR s) s.mem v.mem := by rw [hm2]; exact hM1
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16) (WP.keep [.rax, .r10] (Q := fun y =>
      y.mem = (v.mem.writeW (off (fb s) 8) (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))).writeW (fb s)
      (off S (8 * kw (s.gpr .rsi).toNat))) ?_ rfl))
    fun y ⟨⟨hm3, k3⟩, f3⟩ => ?_
  · xrun [cA3, ea_sp, L2.rsp, L2.ld (d := sK) (by decide), L2.ld (d := sScrLen) (by decide),
      L2.st (d := 8) (by decide), hst0,
      R2.rd (d := sK) 17 rfl (by decide), R2.rd (d := sScrLen) 22 rfl (by decide), hcx2]
    have e1 : (s.gpr .rsi + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 = BitVec.ofNat 64 (kw (s.gpr .rsi).toNat) := by
      rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 from rfl]
      unfold kw
      generalize s.gpr .rsi = x at *
      bv_omega
    have e2 : BitVec.ofNat 64 (kw (s.gpr .rsi).toNat) <<< 3 + S = off S (8 * kw (s.gpr .rsi).toNat) := by
      rw [BitVec.add_comm]; simp only [off]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      unfold kw; rw [Nat.shiftLeft_eq]; omega
    simp only [upd, Nat.reduceEqDiff, ite_false, h17, h22, e1, e2]
  have R3 : Rep y.mem (fb s) S V (upd (upd (upd W 33 (accV lo (V 0))) 1
      (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))) 0 (off S (8 * kw (s.gpr .rsi).toNat))) := by
    rw [hm3]; exact Rb
  have L3 : Lay y (fb s) S := L2.of_rep' R2 R3 (by simp [upd]) (k3.gpr (by decide)) k3.2.2
  have hM3 := vframe_keep hp.toVPre (k2.2.2.trans (k1.2.2.trans hw)) L2.rsp hM2 f3
  refine WP.mono (cA4_ok hp L3 R3 (k3.2.1.trans (k2.2.1.trans (k1.2.1.trans hrd))) hM3) fun z ⟨L4, k4, R4, hM4⟩ => ?_
  refine WP.mono (WP.keep [.rcx] (Q := fun w => w.mem = z.mem ∧ w.gpr .rcx = BitVec.ofNat 64 eb) ?_ rfl)
    fun w ⟨⟨hm5, hcx⟩, k5⟩ => ?_
  · xrun [cA5, ea_sp, L4.rsp, L4.ld (d := sBits) (by decide), R4.rd (d := sBits) 27 rfl (by decide)]
    simp [upd, h27]
  have R5 : Rep w.mem (fb s) S V (chkW W s lo (V 0)) := by rw [hm5]; exact R4
  have k35 : Keep [.rax, .r10, .rax, .rcx] v w := (k3.trans k4).trans k5
  refine ⟨L4.congr (k5.gpr (by decide)) k5.2.2 (by rw [hm5]), ((k1.trans k2).trans k35).mono (by decide), R5,
    by rw [hm5]; exact hM4, ?_, ?_, ?_, hcx, ?_, ?_⟩ <;>
    rw [k35.gpr (by decide)] <;> with_reducible assumption


/-! ## The call -/

/-- A table's word, read from memory that changed only in the writable
regions and below the frame. -/
theorem vtab_read {s : State} (hp : Pre tsH tsG s) {m : Mem} (hM : Frame (vwrR s) s.mem m) {i o : Nat}
    (hi : i = 8 ∨ i = 9) (ho : o + 8 ≤ 40) :
    m.readW (off (stackArg s i) o) 64 = s.mem.readW (off (stackArg s i) o) 64 := by
  have sH : Region.Sub ⟨stackArg s 8, 40⟩ ⟨stackArg s 8, 88⟩ := Region.sub_prefix (by decide)
  have hw : (stackArg s i).toNat + 40 ≤ 2 ^ 64 := by rcases hi with rfl | rfl <;> [have := hp.wTH; have := hp.wTG] <;> omega
  refine hM.readW (r := ⟨stackArg s i, 40⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)
  simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hi with rfl | rfl <;> rcases hr with rfl | rfl
  · exact (hp.dKtH.sub_right sH).symm
  · exact (hp.dstH.sub_right sH).symm
  · exact hp.dKtG.symm
  · exact hp.dstG.symm

/-- The index of the table `hash`'s hash function, at word 5 of the table. -/
theorem vidx_read {s : State} (hp : Pre tsH tsG s) {m : Mem} (hM : Frame (vwrR s) s.mem m) :
    m.readW (off (stackArg s 8) 40) 64 = s.mem.readW (off (stackArg s 8) 40) 64 := by
  have hw := hp.wTH
  refine hM.readW (r := ⟨stackArg s 8, 88⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)
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
  [⟨s.gpr .r8, T.H.D⟩, ⟨off (stackArg s 4) lo, el⟩, ⟨stackArg s 8, 40⟩, ⟨stackArg s 9, 40⟩, ⟨fb s, 32⟩]

/-- What it writes: its working space, after the output. -/
def kWr (s : State) : List Region :=
  [⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat),
    (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩]

theorem kw_le {k : Nat} : k ≤ 8 * kw k := by unfold kw; omega

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
  have hE0 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 0) (by decide)).trans E.w0
  have hE1 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 1) (by decide)).trans E.w1
  have hE2 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 2) (by decide)).trans E.w2
  have hE3 := (vstackArg_call hp.toVPre hsp (kRd T s lo el) (kWr s) (i := 3) (by decide)).trans E.w3
  have hlo := E.hlo; have heb1 := E.eb1; have heb2 := E.eb2; have hel := E.hel
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := E.M.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
  have hTab : TabsAt T.H T.dn T.f T.G T.g (stackArg s 8) (stackArg s 9)
      (t.callEntry.withRegions (kRd T s lo el) (kWr s)) :=
    TabsAt.vframe (t := t.callEntry.withRegions (kRd T s lo el) (kWr s)) hp E.tabs fSE (E.sy ▸ rfl)
  simp only [chkK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    E.di, E.si, E.dx, E.cx, hsp, stackArgAddr_call hsp, hE0, hE1, hE2, hE3]
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  have hcs : chkStack = 408 := rfl
  have c2 : oRsa = 8192 := rfl
  have h8' := vfb_sub8 hp.toVPre
  have hkw := kw_le (k := (s.gpr .rsi).toNat)
  have hkw2 : kw (s.gpr .rsi).toNat ≤ 128 := by unfold kw; omega
  have hsc : (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 5).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega
  have hel2 : el ≤ 1024 := by omega
  have toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]
  have hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega
  have heb' : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega
  rw [hel', heb', E.hD]
  have hsk : (kw (s.gpr .rsi).toNat) * 8 ≤ (stackArg s 5).toNat * 8 := by unfold kw at *; omega
  -- What lies in what.
  have sI : Region.Sub ⟨off (stackArg s 4) lo, el⟩ (vscrR s) := Offset.sub_base _ (by omega)
  have sR : Region.Sub ⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat),
      (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold kw at *; omega)
  have sA : Region.Sub ⟨fb s, 32⟩ (vstkR s) := fun a h => vframe_sub s a (Region.sub_prefix (by decide) a h)
  have sRet : Region.Sub ⟨fb s - 8, 8⟩ (vstkR s) := vret8_sub s
  have sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 chkStack, chkStack⟩ (vstkR s) := by
    simp only [vstkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have sH : Region.Sub ⟨stackArg s 8, 40⟩ ⟨stackArg s 8, 88⟩ := Region.sub_prefix (by decide)
  have dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega)).symm
  have dKA : (⟨fb s - 8 - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    refine Region.Disjoint.sub_left (Offset.base_disjoint_below (fb s) (n := 416) (k := 32) (by omega)).symm ?_
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have dIR : (⟨off (stackArg s 4) lo, el⟩ : Region).Disjoint
      ⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat), (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega)) (by omega) (by rw [hsc]; unfold kw at *; omega)
  have hsA : (vscrR s).Disjoint ⟨fb s, 32⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by unfold chkStack; omega, by omega, by rw [kRd, E.hD], rfl,
    hp.ddgs.sub_right sR, dIR, hsA.sub_left sR,
    hp.dKdg.sub_left sRet, (hp.dKs.sub_left sRet).sub_right sI, (hp.dKs.sub_left sRet).sub_right sR, dRA,
    hp.dKdg.sub_left sStk, (hp.dKs.sub_left sStk).sub_right sI, (hp.dKs.sub_left sStk).sub_right sR, dKA,
    hp.wDg, by rw [toNat_off (by omega)]; omega, by rw [toNat_off (by omega), hsc]; unfold kw at *; omega,
    heb1, heb2, hel, by rw [hsc]; unfold Proof.RsaPss.encodingScratchWords kw at *; omega,
    (hp.dstH.sub_left sR).sub_right sH, hp.dstG.sub_left sR, (hp.dKtH.sub_left sRet).sub_right sH,
    hp.dKtG.sub_left sRet, (hp.dKtH.sub_left sStk).sub_right sH, hp.dKtG.sub_left sStk,
    by have := hp.wTH; omega, hp.wTG, hTab⟩

theorem ck_covers {T : Tabs} {s t : State} (hp : Pre tsH tsG s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    {lo el : Nat} (hlo : lo + el ≤ (s.gpr .rsi).toNat) (hD : T.H.D = (s.gpr .r9).toNat) :
    Covers (kRd T s lo el ++ kWr s) (t.rd ++ t.wr) ∧ Covers (kWr s) t.wr := by
  have hsl := hp.hsl; have hk2 := hp.k2
  have hsc : (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 5).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (kWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, hscr, 8 * kw (s.gpr .rsi).toNat, rfl, by dsimp only; rw [hsc]; unfold kw at *; omega⟩
  have hin : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [hrd]; exact hx)
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [kRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, hin _ (by rw [hp.hrdE]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hscr, lo, rfl, by dsimp only; omega⟩
  · exact ⟨⟨stackArg s 8, 88⟩, hin _ (by rw [hp.hrdE]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨⟨stackArg s 9, 40⟩, hin _ (by rw [hp.hrdE]; simp), 0, z _, by dsimp only; omega⟩
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
  have hst := E.sp; have hrd := E.rd; have hwr := E.wr; have hM := E.M
  have hlo := E.hlo; have hel := E.hel; have heb2 := E.eb2
  obtain ⟨hc, hw⟩ := ck_covers (T := T) hp hrd hwr hlo E.hD
  refine X86_64.WP.of_syms (X86_64.WP.callF hv hspC (by unfold chkStack at hd; omega)
    (ck_pre (Hs := Hs) (Gs := Gs) hp E) hc hw ?_)
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx hsy
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  have c2 : oRsa = 8192 := rfl
  have hkw := kw_le (k := (s.gpr .rsi).toNat)
  have hkw2 : kw (s.gpr .rsi).toNat ≤ 128 := by unfold kw; omega
  have hsc : (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 5).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega
  rw [hst] at hf
  have sR : Region.Sub ⟨off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat),
      (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold kw at *; omega)
  have sBel : Region.Sub (below (fb s) (chkC.x86_64Depth + 8)) (vstkR s) := by
    simp only [below, fb, vstkR, sub_sub']
    exact Offset.sub_below _ (by unfold chkStack at hd; omega) (by unfold chkStack at hd; omega)
  have dFb : (frR s).Disjoint (below (fb s) (chkC.x86_64Depth + 8)) :=
    Offset.base_disjoint_below (fb s) (by unfold chkStack at hd; omega)
  have hS8 : Region.Sub ⟨stackArg s 4, oRsa⟩ (vscrR s) := Region.sub_prefix (by omega)
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), hsy.trans E.sy, ?_, ?_⟩
  · simp only [kWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sR⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · refine R.of_call hp.geo (fun x hx hin => hf x fun r hr hc => ?_) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'; dsimp only; omega)
    simp only [kWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rcases hin with hin | hin
      · refine hx _ (List.mem_singleton_self _) ?_
        have h1 := (Offset.lt_iff x (stackArg s 4) (d := 8 * kw (s.gpr .rsi).toNat)
          (n := (stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8)
          (by rw [hsc]; unfold kw at *; omega)).mp (by simp only [Region.Contains, off] at hc; omega)
        have h2 : (x - stackArg s 4).toNat < oRsa := by simp only [Region.Contains] at hin; omega
        show (x - (stackArg s 4 + BitVec.ofNat 64 (8 * kw (s.gpr .rsi).toNat))).toNat + 1 ≤
          oRsa - 8 * kw (s.gpr .rsi).toNat
        have := (Offset.lt_iff x (stackArg s 4) (d := 8 * kw (s.gpr .rsi).toNat)
          (n := oRsa - 8 * kw (s.gpr .rsi).toNat) (by omega)).mpr ⟨h1.1, by omega⟩
        omega
      · exact (hp.dKs.sub_left (vframe_sub s)) x hin (sR x hc)
    · rcases hin with hin | hin
      · exact hp.dKs x (sBel x hc) (hS8 x hin)
      · exact dFb x hin hc
  · have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
 rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
    have hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega
    have heb' : (BitVec.ofNat 64 eb).toNat = eb := by
      rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega
    simp only [chkK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      E.di, E.si, E.dx, E.cx, E.r8, E.r9, hg₂ .rax (by decide), hel', heb'] at hpost
    rw [E.hD] at hpost ⊢
    rw [bytesAt_frame fSE (p := s.gpr .r8) (len := (s.gpr .r9).toNat) (vin_apart hp.dKdg hp.ddgs)
        (by have := hp.wDg; omega),
      bytesAt_frame fE (p := off (stackArg s 4) lo) (len := el) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ((hp.dKs.sub_left (vret8_sub s)).sub_right (Offset.sub_base _ (by omega) :
          Region.Sub ⟨off (stackArg s 4) lo, el⟩ (vscrR s))).symm) (by omega)] at hpost
    exact hpost


end VG.Proof.RsaPss.X86_64.Pc
