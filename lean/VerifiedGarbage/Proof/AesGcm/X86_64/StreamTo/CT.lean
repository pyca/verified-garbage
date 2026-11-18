module

import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
meta import VerifiedGarbage.Proof.Gcm.StreamTo
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.CallSp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Spec.Aes
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `AesGcm.X86_64.StreamTo.Head`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.StreamTo.Rest`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.StreamTo.Copy`, which this module and modules that import it used -/

section

/-!
# AES-GCM streaming encryption out of place, x86-64: copying bytes

Untrusted: everything here is checked by Lean. `copyLoop_ok` for any number
of bytes below 2⁶⁴ (`copyLoopL_ok`), as the plaintext left may be.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- What `copyLoop` needs of the state: `LoopPre`, with fewer than 2⁶⁴ bytes. -/
structure CopyPre (s : State) (S D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_keptL {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 64) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega_using [hi]) (by omega_using [hi, hn])) (Region.sub_prefix (by omega_using [hi]) _ hcon)

theorem copyLoopL_ok (s : State) {S D : Addr} {n : Nat} (h : CopyPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, r10₁, by simp [bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t
    (by rw [g _ (by decide) (by decide), h.rsi]) (by rw [g _ (by decide) (by decide), h.rdi]) r10
    (by rw [g _ (by decide) (by decide), h.rcx])
    (by rw [rd, wr]; exact in_of_covers h.rd hi h.lt)
    (by rw [wr]; exact in_of_covers h.wr hi h.lt)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem S i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, src_keptL h.disj hi h.lt _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; have := h.lt; omega_using [hi, this]), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega_using [hi, this]) (by have := h.lt; omega_using [this])]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], by rw [r10', succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-! ### `AesGcm.X86_64.StreamTo.EncCall`, which only this module used -/

section

/-!
# AES-GCM streaming encryption out of place, x86-64: the call of the bytes left

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_stream_encrypt` on the `L - o` bytes left at `Dst + o`, with
their number pushed for it (`encCall_ok`): what it needs, from the layout of
`s` (`encPre`), and what it leaves.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

/-- `n` bytes of the output, after `o` done. -/
abbrev dqR (o n : Nat) : Region := ⟨Dst s + BitVec.ofNat 64 o, n⟩

/-- What the call reads and writes. -/
abbrev encRd (M : CtxMode) : List Region := [kR M s, ⟨SP s - BitVec.ofNat 64 8, 8⟩]
abbrev encWr (o n : Nat) : List Region := [stR s, dqR s o n]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem dq_sub {o n : Nat} (hn : o + n ≤ L s) : (dqR s o n).Sub (dR s) := Offset.sub_base _ hn

/-- What the call of `vg_aes_gcm_stream_encrypt` needs. -/
theorem encPre {o n : Nat} (hn : o + n ≤ L s) {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 16) (hrd : u.rd = encRd s M) (hwr : u.wr = encWr s o n)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = St s)
    (h_9 : u.gpr .r9 = Dst s + BitVec.ofNat 64 o) (a0 : stackArg u 0 = BitVec.ofNat 64 (n))
    (hok : M.ok u.mem (K s)) :
    (encK M).pre u := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  obtain hnn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain ds := dq_sub (s := s) hn
  obtain hargs : (Proof.AesGcm.args u 1) = ⟨SP s - BitVec.ofNat 64 8, 8⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  obtain hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 16, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  obtain hstk : below (SP s - BitVec.ofNat 64 16) 2608 = ⟨SP s - BitVec.ofNat 64 2624, 2608⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  obtain tA : Region.Sub ⟨SP s - BitVec.ofNat 64 8, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 16, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tS : Region.Sub ⟨SP s - BitVec.ofNat 64 2624, 2608⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain hsp16 : (SP s - BitVec.ofNat 64 16).toNat = (SP s).toNat - 16 := toNat_sub_ofNat (by omega_arith)
  obtain hsp8 : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega_arith)
  obtain hsp2624 : (SP s - BitVec.ofNat 64 2624).toNat = (SP s).toNat - 2624 := toNat_sub_ofNat (by omega_arith)
  obtain d₁ : (⟨SP s - BitVec.ofNat 64 16, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 8, 8⟩ :=
    Offset.disjoint_of_le (by simp only [hsp16, hsp8]; omega_arith) (by simp only [hsp8]; omega_arith)
  obtain d₂ : (⟨SP s - BitVec.ofNat 64 2624, 2608⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 8, 8⟩ :=
    Offset.disjoint_of_le (by simp only [hsp2624, hsp8]; omega_arith) (by simp only [hsp8]; omega_arith)
  simp only [encK, encCallPre, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_9, a0, hnn,
    hrsp, Proof.AesGcm.rounds, hstk]
  refine ⟨trivial, trivial, hp.k_st, hp.k_d.sub_right ds, hp.st_d.sub_right ds, hp.b_st.symm.sub_right tA,
    hp.b_d.symm.sub_left ds |>.sub_right tA,
    hp.b_k.sub_left tR', hp.b_st.sub_left tR', (hp.b_d.sub_left tR').sub_right ds,
    d₁,
    hp.b_k.sub_left tS, hp.b_st.sub_left tS, (hp.b_d.sub_left tS).sub_right ds,
    d₂,
    hp.w_k, hp.w_st, off_bound hp.w_d hn, by rw [hsp16]; omega_arith, by rw [hsp16]; omega_arith, hp.rounds,
    hok⟩

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

/-- What the call of `vg_aes_gcm_stream_encrypt` needs, after the push. -/
theorem encEntry {o n : Nat} (hn : o + n ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_9 : st.gpr .r9 = Dst s + BitVec.ofNat 64 o) (h_10 : st.gpr .r10 = BitVec.ofNat 64 (n)) :
    (encK M).pre ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) ∧
      Covers (encRd s M ++ encWr s o n) ((pushed [.r10] st).rd ++ (pushed [.r10] st).wr) ∧
      Covers (encWr s o n) (pushed [.r10] st).wr ∧
      stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) 0 = BitVec.ofNat 64 (n) := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain hn8 : 8 * [Reg.r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.r10] (by decide) hn8
  obtain hP : (pushed [.r10] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 16, 8⟩] (pushed [.r10] st).mem (pushed [.r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain fU : Frame (wR s ++ [tR s]) s.mem (pushed [.r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega_arith)
  obtain a0 : stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) 0 = BitVec.ofNat 64 (n) := by
    rw [stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith), show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * 0) =
      SP s - BitVec.ofNat 64 (8 * (0 + 1)) by simp, ← hsp]
    exact (hpj 0 (by decide)).trans h_10
  obtain gU : ∀ r, r ≠ .rsp → ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr .rsp = SP s - BitVec.ofNat 64 16 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain hok : M.ok ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).mem (K s) := by
    rw [State.withRegions_mem]; exact M.frame fU (k_disj hp) hp.w_k hp.ok
  obtain hpre := encPre hp hn hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_9) a0 hok
  obtain hPw : (pushed [.r10] st).wr = ⟨SP s - BitVec.ofNat 64 8, 8⟩ :: wR s := by
    rw [pushed_wr, hsp, hwr, hp.wr]; rfl
  obtain hPr : (pushed [.r10] st).rd = [kR M s, srcR s, aR s] := by rw [pushed_rd, hrd, hp.rd]
  obtain cDq : ∀ {ts : List Region}, dR s ∈ ts → Covers [dqR s o n] ts := fun h =>
    covers_off (k := L s) (d := o) (m := n) h (by omega_arith) (by omega_arith)
  obtain cw : Covers (encWr s o n) (pushed [.r10] st).wr := by
    rw [hPw]; exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (cDq (by simp)) covers_nil')
  obtain cr : Covers (encRd s M ++ encWr s o n) ((pushed [.r10] st).rd ++ (pushed [.r10] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (cDq (by simp)) covers_nil')))
  exact ⟨hpre, cr, cw, a0⟩

/-- The call of `vg_aes_gcm_stream_encrypt` on the `L - o` bytes left at
`Dst + o`, with their number pushed for it. -/
theorem encCall_ok (E : EncFn M) {o n : Nat} (hn : o + n ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_cx : st.gpr .rcx = AL s) (h_8 : st.gpr .r8 = TL s + BitVec.ofNat 64 o)
    (h_9 : st.gpr .r9 = Dst s + BitVec.ofNat 64 o) (h_10 : st.gpr .r10 = BitVec.ofNat 64 (n)) :
    WP isa (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (encWr s o n ++ [tR s]) st.mem st'.mem ∧
      ∀ iv a p, StreamRepr st.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) p) →
        AL s = BitVec.ofNat 64 a.length → (TL s + BitVec.ofNat 64 o).toNat = p.length →
        StreamRepr st'.mem (St s) (ciph s) (hk s) iv a
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (n))) ∧
          bytesAt st'.mem (Dst s + BitVec.ofNat 64 o) (n) =
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (n))).drop
              p.length := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain hn8 : 8 * [Reg.r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.r10] (by decide) hn8
  obtain hP : (pushed [.r10] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 16, 8⟩] (pushed [.r10] st).mem (pushed [.r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain fU : Frame (wR s ++ [tR s]) s.mem (pushed [.r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega_arith)
  obtain a0 : stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) 0 = BitVec.ofNat 64 (n) := by
    rw [stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith), show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * 0) =
      SP s - BitVec.ofNat 64 (8 * (0 + 1)) by simp, ← hsp]
    exact (hpj 0 (by decide)).trans h_10
  obtain gU : ∀ r, r ≠ .rsp → ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr .rsp = SP s - BitVec.ofNat 64 16 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain ⟨hpre, cr, cw, -⟩ := encEntry hp hn hsp hrd hwr hf h_di h_si h_dx h_9 h_10
  -- What the push and the return address leave as it was.
  obtain fS : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩, ⟨SP s - BitVec.ofNat 64 16, 8⟩] st.mem
      (pushed [.r10] st).callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  obtain outT : ∀ {r : Region}, r.Disjoint (tR s) →
      ∀ r' ∈ [(⟨SP s - BitVec.ofNat 64 8, 8⟩ : Region), ⟨SP s - BitVec.ofNat 64 16, 8⟩], r.Disjoint r' := by
    intro r hd r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
  obtain dsq := dq_sub (s := s) hn
  obtain eD : bytesAt (pushed [.r10] st).callEntry.mem (Dst s + BitVec.ofNat 64 o) (n) =
      bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (n) :=
    bytesAt_frame fS (outT (hp.b_d.symm.sub_left dsq)) (by omega_arith)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := encK M)
    E.ok E.sp (by have := E.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  obtain r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [encK, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.arg, a0, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), gU _ (by decide : Reg.rdx ≠ .rsp),
    gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp), gU _ (by decide : Reg.r9 ≠ .rsp),
    h_di, h_si, h_dx, h_cx, h_8, h_9, hm₂, ciph_eq hp fU, hk_eq hp fU, eD] at hpost
  obtain hnn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  rw [hnn] at hpost
  refine ⟨r₃, hwr', fun m u fm => ?_⟩
  -- The `pop` loses the frame's 8 bytes, in the stack below `SP`, apart from
  -- the outputs.
  obtain fm' : Frame [tR s] s'.mem m := by
    rw [hsp] at fm
    exact fm.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, List.mem_singleton_self _, stk_sub (s := s) (by decide) (by decide)⟩
  dsimp only
  refine ⟨fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, fun iv a p hr hal hpl => ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · refine Frame.trans ?_ (fm'.sub fun r hr => ⟨tR s, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
    obtain b2616 : Region.Sub (below ((pushed [.r10] st).gpr .rsp) (E.fn.code.x86_64Depth + 8)) (tR s) := by
      obtain h₁ := below_sub (sp := (pushed [.r10] st).gpr .rsp) (a := E.fn.code.x86_64Depth + 8) (b := 2616)
        (by have := E.xd; omega_arith) (by decide)
      obtain e : below (SP s - BitVec.ofNat 64 8) 2616 = ⟨SP s - BitVec.ofNat 64 2624, 2616⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨tR s, by simp, b2616⟩
  · have := hpost iv a p (streamRepr_frame fS (outT hp.b_st.symm) hr) hal hpl
    rw [eD] at this
    obtain ⟨r₁, r₂⟩ := this
    refine ⟨streamRepr_frame fm' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.b_st.symm) r₁, ?_⟩
    rw [bytesAt_frame fm' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.b_d.symm.sub_left dsq) (by omega_arith)]
    exact r₂

end

end VG.Proof.AesGcm.X86_64.StreamTo

end

end


/-!
# AES-GCM streaming encryption out of place, x86-64: the bytes left

Untrusted: everything here is checked by Lean. `rest` from `Mid s o`: the
`L - o` bytes left, if any, copied from the plaintext to the output and
encrypted there by `vg_aes_gcm_stream_encrypt` as the continuation of the
text so far and the first `o` bytes, make the whole encryption (`rest_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.streamToPost s s'

/-- The encryption of a text in two pieces, past the first `k ≤ |x|` bytes. -/
theorem gctr_drop (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb : Spec.Gcm.Block) {x y : List Byte} {k : Nat}
    (hk : k ≤ x.length) :
    (gctr ciph icb (x ++ y)).drop k = (gctr ciph icb x).drop k ++ (gctr ciph icb (x ++ y)).drop x.length := by
  rw [Proof.Gcm.gctr_append, List.drop_append_of_le_length (by rw [Proof.Gcm.length_gctr]; exact hk),
    List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- `work` from the stack, and the bytes left, `L - o`. -/
theorem restHead_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .rcx = BitVec.ofNat 64 (L s - o) ∧ st'.gpr .rax = BitVec.ofNat 64 o ∧
      st'.zf = some (decide (L s - o = 0)) ∧
      (∀ r, r ≠ .r11 → r ≠ .rcx → r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  obtain a₃ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 3) (by decide)
  obtain hW : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
    rw [h.rsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₆ := slot_in hp h.rd h.wr (d := 48) (by decide)
  obtain r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  obtain hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  obtain hsub := ofNat_sub ho hL
  obtain hz := and_self_beq (show L s - o < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [wLen, wDone]; xrun [a₃, hW, r₆, r₈, hlen, h.kept.done, hsub], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, hsub]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hsub, hz]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The pointers of the copy: past the `o` bytes done. -/
theorem restPtrs_ok {o : Nat} {st : State} (h : Mid s o st) (h11 : st.gpr .r11 = W s)
    (hax : st.gpr .rax = BitVec.ofNat 64 o) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax), .mov .rdi (.mem (at_ .r11 wDst)),
      .alu .add .rdi (.reg .rax)]) st fun st' =>
      st'.gpr .rsi = Src s + BitVec.ofNat 64 o ∧ st'.gpr .rdi = Dst s + BitVec.ofNat 64 o ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain r₅ := slot_in hp h.rd h.wr (d := 40) (by decide)
  obtain r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [wSrc, wDst]; xrun [h11, hax, r₅, r₇, h.kept.src, h.kept.dst], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags]
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The arguments of `vg_aes_gcm_stream_encrypt` on the bytes left. -/
theorem restArgs_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block restArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s ∧ st'.gpr .rcx = AL s ∧
      st'.gpr .r8 = TL s + BitVec.ofNat 64 o ∧ st'.gpr .r9 = Dst s + BitVec.ofNat 64 o ∧
      st'.gpr .r10 = BitVec.ofNat 64 (L s - o) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  obtain a₃ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 3) (by decide)
  obtain hW : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
    rw [h.rsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₀ := slot_in hp h.rd h.wr (d := 0) (by decide)
  obtain r₁ := slot_in hp h.rd h.wr (d := 8) (by decide)
  obtain r₂ := slot_in hp h.rd h.wr (d := 16) (by decide)
  obtain r₃ := slot_in hp h.rd h.wr (d := 24) (by decide)
  obtain r₄ := slot_in hp h.rd h.wr (d := 32) (by decide)
  obtain r₆ := slot_in hp h.rd h.wr (d := 48) (by decide)
  obtain r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  obtain r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  obtain k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  obtain hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  obtain hsub := ofNat_sub ho hL
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [restArgs, wCtx, wRounds, wState, wAad, wTlen, wLen, wDst, wDone]
    xrun [a₃, hW, r₀, r₁, r₂, r₃, r₄, r₆, r₇, r₈, k0, h.kept.rounds, h.kept.st, h.kept.aad, h.kept.tl, hlen,
      h.kept.dst, h.kept.done, hsub],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags, hsub]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The return address is apart from what the code writes. -/
theorem ret_disj : ∀ r ∈ wR s ++ [tR s], (⟨SP s, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.t_st, hp.t_d, hp.t_w, Offset.base_disjoint_below _ (by have := hp.w_sp; omega_arith)]

/-- With every byte done, `Mid` is the end. -/
theorem done_of {st : State} (h : Mid s (L s) st) : Done s st :=
  ⟨⟨h.saved, h.frame.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩,
    fun iv a p hr hal hpl => h.sem iv a p hr hal hpl⟩

/-- `Mid` through the copy, which writes only `n` bytes of the output past
the `o` bytes done. -/
theorem Mid.copy {o n : Nat} {st st' : State} (h : Mid s o st) (hn : o + n ≤ L s)
    (hf : Frame [dqR s o n] st.mem st'.mem) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r)
    (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) (hmx : st'.mxcsr = st.mxcsr) : Mid s o st' := by
  obtain ds := dq_sub (s := s) hn
  obtain one : ∀ {r : Region}, r.Disjoint (dqR s o n) → ∀ r' ∈ [dqR s o n], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨h.o_le, h.tl, by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr],
    hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf (one ((hp.d_w.symm.sub_left kR'_sub).sub_right ds)),
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, ds⟩),
    fun iv a p hr hal hpl => ?_, hmx.trans h.mx⟩
  obtain ⟨sr, dd⟩ := h.sem iv a p hr hal hpl
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  refine ⟨streamRepr_frame hf (one (hp.st_d.sub_right ds)) sr, ?_⟩
  rw [← dd]
  exact bytesAt_frame hf (one (Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega_arith))) (by omega_arith)

/-- `rest`, from `Mid s o`: the end. -/
theorem rest_ok (E : EncFn M) {o : Nat} {st : State} (h : Mid s o st) : WP isa (rest E.fn) st (Done s) := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  unfold rest
  refine WP.seq (WP.mono_mx (by decide) (restHead_ok hp h) fun s₁ ⟨r11₁, cx₁, ax₁, z₁, g₁, m₁, rd₁, wr₁⟩ mx_s₁ => ?_)
  obtain M₁ : Mid s o s₁ := h.regs m₁ (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₁ wr₁ mx_s₁
  refine WP.ite (decide (L s - o = 0)) (by simp only [eval, z₁]) (fun e => ?_) (fun e => ?_)
  · have hoL : o = L s := by simp at e; omega_arith
    exact WP.block_nil (done_of hp (hoL ▸ M₁))
  obtain hlt : o < L s := by simp at e; omega_arith
  refine WP.seq (WP.mono_mx (by decide) (restPtrs_ok hp M₁ r11₁ ax₁) fun s₂ ⟨si₂, di₂, g₂, m₂, rd₂, wr₂⟩ mx_s₂ => ?_)
  obtain M₂ : Mid s o s₂ := M₁.regs m₂ (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂ mx_s₂
  obtain ds := dq_sub (s := s) (o := o) (n := L s - o) (by omega_arith)
  obtain ss : Region.Sub ⟨Src s + BitVec.ofNat 64 o, L s - o⟩ (srcR s) := Offset.sub_base _ (by omega_arith)
  obtain cp : CopyPre s₂ (Src s + BitVec.ofNat 64 o) (Dst s + BitVec.ofNat 64 o) (L s - o) :=
    ⟨si₂, di₂, by rw [g₂ _ (by decide) (by decide), cx₁], by omega_arith, by omega_arith,
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.rd, M₂.wr, hp.rd]; simp) (by omega_arith) (by omega_arith),
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.wr, hp.wr]; simp) (by omega_arith) (by omega_arith),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.seq (WP.mono_mx (by decide) (copyLoopL_ok s₂ cp) fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ mx_s₃ => ?_)
  obtain f₃ : Frame [dqR s o (L s - o)] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain M₃ : Mid s o s₃ := M₂.copy hp (by omega_arith) f₃ (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃ mx_s₃
  obtain hX₃ : bytesAt s₃.mem (Dst s + BitVec.ofNat 64 o) (L s - o) = bytesAt s.mem (Src s + BitVec.ofNat 64 o) (L s - o) := by
    obtain e := bytesAt_writeBytes_self s₂.mem (Dst s + BitVec.ofNat 64 o)
      (bytesAt s₂.mem (Src s + BitVec.ofNat 64 o) (L s - o)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at e
    rw [m₃, e]
    exact bytesAt_frame M₂.frame (fun r hr => (r_disj hp r hr).sub_left ss) (by omega_arith)
  refine WP.seq (WP.mono_mx (by decide) (restArgs_ok hp M₃) fun s₄ ⟨di, si, dx, cx, r8, r9, r10, cs₄, m₄, rd₄, wr₄⟩ mx_s₄ => ?_)
  obtain M₄ : Mid s o s₄ := M₃.regs m₄ cs₄ rd₄ wr₄ mx_s₄
  refine WP.mono (encCall_ok hp E (n := L s - o) (by omega_arith) M₄.rsp M₄.rd M₄.wr M₄.frame di si dx cx r8 r9 r10)
    fun s₅ ⟨cs₅, rd₅, wr₅, f₅, post⟩ => ?_
  obtain f₅' : Frame (wR s ++ [tR s]) s.mem s₅.mem := M₄.frame.trans (f₅.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨stR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, ds⟩
    · exact ⟨tR s, by simp, fun _ h => h⟩)
  refine ⟨⟨fun r hr => by rw [cs₅ r hr, M₄.saved r hr],
    f₅'.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩, fun iv a p hr hal hpl => ?_⟩
  obtain ⟨sr₄, dd₄⟩ := M₄.sem iv a p hr hal hpl
  obtain hpl' : (TL s + BitVec.ofNat 64 o).toNat = (p ++ pt s o).length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt M₄.tl,
      List.length_append, length_bytesAt]
    show (TL s).toNat + o = p.length + o
    rw [hpl]
  obtain ⟨sr₅, dd₅⟩ := post iv a (p ++ pt s o) sr₄ hal hpl'
  rw [m₄, hX₃] at sr₅ dd₅
  obtain hP : p ++ bytesAt s.mem (Src s) (L s) = p ++ pt s o ++ bytesAt s.mem (Src s + BitVec.ofNat 64 o) (L s - o) := by
    rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' ho]
  show StreamRepr s₅.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (Src s) (L s))) ∧
    bytesAt s₅.mem (Dst s) (L s) = (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (Src s) (L s))).drop p.length
  rw [hP]
  refine ⟨sr₅, ?_⟩
  obtain hD : bytesAt s₅.mem (Dst s) o = bytesAt s₄.mem (Dst s) o := by
    refine bytesAt_frame f₅ (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact (hp.st_d.symm.sub_left (Region.sub_prefix ho))
    · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega_arith)
    · exact hp.b_d.symm.sub_left (Region.sub_prefix ho)
  rw [← Nat.add_sub_cancel' ho, bytesAt_add, Nat.add_sub_cancel' ho, hD, dd₄, dd₅,
    gctr_drop (x := p ++ pt s o) (k := p.length) _ _ (by rw [List.length_append]; omega_arith)]

end

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-!
# AES-GCM streaming encryption out of place, x86-64: the head

Untrusted: everything here is checked by Lean. `head` from `Mid s 0`: if the
text so far ends inside a block, the `Hd` bytes that end it (or all the
plaintext, if fewer), unless the text so far and they would exceed 2⁶⁴
bytes, copied from the plaintext to the output and encrypted there by
`vg_aes_gcm_stream_encrypt` as the continuation of the text so far, leave
`Mid s Hd`; otherwise nothing is done (`head_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- `Mid` through a write of the slot of the head. -/
theorem Mid.slot {o : Nat} {st st' : State} (h : Mid s o st) (hf : Frame [hR s] st.mem st'.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr)
    (hmx : st'.mxcsr = st.mxcsr) : Mid s o st' := by
  have one : ∀ {r : Region}, r.Disjoint (hR s) → ∀ r' ∈ [hR s], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  refine ⟨h.o_le, h.tl, by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr],
    hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf (one kR'_hR),
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, hR_sub⟩),
    fun iv a p hr hal hpl => ?_, hmx.trans h.mx⟩
  obtain ⟨sr, dd⟩ := h.sem iv a p hr hal hpl
  refine ⟨streamRepr_frame hf (one (hp.st_w.sub_right hR_sub)) sr, ?_⟩
  rw [← dd]
  exact bytesAt_frame hf (one ((hp.d_w.sub_left (Region.sub_prefix h.o_le)).sub_right hR_sub))
    (by have := h.o_le; omega_using [hL, this])

end

/-! ## The pieces of the head -/

section
variable (s : State)

/-- Before the head: nothing done, `work` in `r11`, the text so far in `r8`. -/
def HB (st : State) : Prop := Mid s 0 st ∧ st.gpr .r11 = W s ∧ st.gpr .r8 = TL s

/-- The slot of the head holds its number of bytes. -/
abbrev HSlot (m : Mem) : Prop := m.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 (Hd s)

/-- Before the copy of the head. -/
def HC (st : State) : Prop :=
  Mid s 0 st ∧ st.gpr .rsi = Src s + BitVec.ofNat 64 0 ∧ st.gpr .rdi = Dst s + BitVec.ofNat 64 0 ∧
    st.gpr .rcx = BitVec.ofNat 64 (Hd s) ∧ HSlot s st.mem

/-- After the copy of the head. -/
def HA (st : State) : Prop :=
  Mid s 0 st ∧ HSlot s st.mem ∧ bytesAt st.mem (Dst s + BitVec.ofNat 64 0) (Hd s) = pt s (Hd s)

/-- Before the call of the head. -/
def HE (st : State) : Prop :=
  HA s st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = TL s + BitVec.ofNat 64 0 ∧ st.gpr .r9 = Dst s + BitVec.ofNat 64 0 ∧
    st.gpr .r10 = BitVec.ofNat 64 (Hd s)

/-- After the call of the head. -/
def HD (st : State) : Prop :=
  (∀ r ∈ calleeSaved, st.gpr r = s.gpr r) ∧ st.gpr .rsp = SP s ∧ st.rd = s.rd ∧ st.wr = s.wr ∧
    Frame (wR s ++ [tR s]) s.mem st.mem ∧ Kept s 0 st.mem ∧ HSlot s st.mem ∧ Sem s (Hd s) st.mem ∧
    st.mxcsr = s.mxcsr

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem notCs' {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem hl_wp {st : State} (h : HB s st) :
    WP isa (.block headLen) st fun st' =>
      HB s st' ∧ st'.gpr .rax = BitVec.ofNat 64 (Hd s) ∧ st'.zf = some (decide (Hd s = 0)) :=
  WP.mono_mx (by decide) (headLen_ok hp h.2.1 h.2.2 h.1.kept h.1.rd h.1.wr) fun _ ⟨ax, z, g, m, rd, wr⟩ mx =>
    ⟨⟨h.1.regs m (fun r hr => g r (notCs' hr).1 (notCs' hr).2.1) rd wr mx, by rw [g _ (by decide) (by decide), h.2.1],
      by rw [g _ (by decide) (by decide), h.2.2]⟩, ax, z⟩

omit hp in
theorem ho_wp {st : State} (h : HB s st ∧ st.gpr .rax = BitVec.ofNat 64 (Hd s)) :
    WP isa (.block headOver) st fun st' =>
      (HB s st' ∧ st'.gpr .rax = BitVec.ofNat 64 (Hd s)) ∧
        st'.cf = some (decide (2 ^ 64 ≤ (TL s).toNat + Hd s)) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  exact WP.mono_mx (by decide) (headOver_ok h.2 h.1.2.2 (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hL))
    fun _ ⟨cf, g, m, rd, wr⟩ mx =>
    ⟨⟨⟨h.1.1.regs m (fun r hr => g r (notCs' hr).2.1) rd wr mx, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, by rw [g _ (by decide), h.2]⟩, cf⟩

theorem hp_wp {st : State} (h : HB s st ∧ st.gpr .rax = BitVec.ofNat 64 (Hd s)) :
    WP isa (.block headPtrs) st (HC s) :=
  WP.mono_mx (by decide) (headPtrs_ok hp h.1.2.1 h.2 h.1.1.kept h.1.1.rd h.1.1.wr)
    fun _ ⟨cx, si, di, k, g, f, rd, wr⟩ mx =>
    ⟨h.1.1.slot hp f (fun r hr => g r (notCs' hr).2.1 (notCs' hr).2.2.2.1 (notCs' hr).2.2.2.2.1) rd wr mx,
      by rw [si, BitVec.add_zero], by rw [di, BitVec.add_zero], cx, k⟩

theorem hc_wp (hk0 : Hd s ≠ 0) {st : State} (h : HC s st) : WP isa copyLoop st (HA s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have hHL : Hd s ≤ L s := Nat.min_le_right _ _
  obtain ⟨M₃, si₃, di₃, cx₃, k₃⟩ := h
  have ds := dq_sub (s := s) (o := 0) (n := Hd s) (by omega_using [hHL])
  have ss : Region.Sub ⟨Src s + BitVec.ofNat 64 0, Hd s⟩ (srcR s) := Offset.sub_base _ (by omega_using [hHL])
  have cp : CopyPre st (Src s + BitVec.ofNat 64 0) (Dst s + BitVec.ofNat 64 0) (Hd s) :=
    ⟨si₃, di₃, cx₃, by omega_using [hk0], by omega_using [hL, hHL],
      covers_off (k := L s) (d := 0) (m := Hd s) (by rw [M₃.rd, M₃.wr, hp.rd]; simp) (by omega_using [hHL]) (by omega_using []),
      covers_off (k := L s) (d := 0) (m := Hd s) (by rw [M₃.wr, hp.wr]; simp) (by omega_using [hHL]) (by omega_using []),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.mono_mx (by decide) (copyLoopL_ok st cp) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ mx₄ => ?_
  have f₄ : Frame [dqR s 0 (Hd s)] st.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  refine ⟨M₃.copy hp (by omega_using [hHL]) f₄ (fun r hr => g₄ r (notCs' hr).1 (notCs' hr).2.2.2.2.2.2.2.1) rd₄ wr₄ mx₄,
    ?_, ?_⟩
  · show s₄.mem.readW _ 64 = _
    rw [← k₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.d_w.sub_left ds).sub_right hR_sub).symm) (by decide)
  · have e := bytesAt_writeBytes_self st.mem (Dst s + BitVec.ofNat 64 0)
      (bytesAt st.mem (Src s + BitVec.ofNat 64 0) (Hd s)) (by rw [length_bytesAt]; omega_using [hL, hHL])
    rw [length_bytesAt] at e
    rw [m₄, e, BitVec.add_zero]
    exact bytesAt_frame M₃.frame (fun r hr => (r_disj hp r hr).sub_left (Region.sub_prefix hHL)) (by omega_using [hL, hHL])

theorem ha_wp {st : State} (h : HA s st) : WP isa (.block headArgs) st (HE s) :=
  WP.mono_mx (by decide) (headArgs_ok hp h.1 h.2.1) fun _ ⟨di, si, dx, cx, r8, r9, r10, cs, m, rd, wr⟩ mx =>
    ⟨⟨h.1.regs m cs rd wr mx, by rw [m]; exact h.2.1, by rw [m]; exact h.2.2⟩, di, si, dx, cx, r8, r9, r10⟩

theorem hcall_wp (E : EncFn M) {st : State} (h : HE s st) :
    WP isa (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) st (HD s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have hHL : Hd s ≤ L s := Nat.min_le_right _ _
  obtain ⟨⟨M₅, k₅, hX₅⟩, di, si, dx, cx, r8, r9, r10⟩ := h
  have ds := dq_sub (s := s) (o := 0) (n := Hd s) (by omega_using [hHL])
  refine WP.mono_mx (call_frame_mx E.mx) (encCall_ok hp E (o := 0) (n := Hd s) (by omega_using [hHL]) M₅.rsp M₅.rd
    M₅.wr M₅.frame di si dx cx r8 r9 r10) fun s₆ ⟨cs₆, rd₆, wr₆, f₆, post⟩ mx₆ => ?_
  have f₆' : Frame (wR s ++ [tR s]) s.mem s₆.mem := M₅.frame.trans (f₆.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨stR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, ds⟩
    · exact ⟨tR s, by simp, fun _ h => h⟩)
  have out : ∀ {r : Region}, r.Sub (wkR s) → ∀ r' ∈ encWr s 0 (Hd s) ++ [tR s], r.Disjoint r' := by
    intro r hs r' hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact hp.st_w.symm.sub_left hs
    · exact (hp.d_w.symm.sub_left hs).sub_right ds
    · exact hp.b_w.symm.sub_left hs
  refine ⟨fun r hr => by rw [cs₆ r hr, M₅.saved r hr], by rw [cs₆ _ (by decide), M₅.rsp], rd₆.trans M₅.rd,
    wr₆.trans M₅.wr, f₆', M₅.kept.frame f₆ (out kR'_sub),
    by show s₆.mem.readW _ 64 = _; rw [← k₅]; exact f₆.readW (Region.contains_self _ _) (out hR_sub) (by decide),
    fun iv a p hr hal hpl => ?_, mx₆.trans M₅.mx⟩
  obtain ⟨sr₅, -⟩ := M₅.sem iv a p hr hal hpl
  have z : pt s 0 = [] := rfl
  rw [z, List.append_nil] at sr₅
  have hpl' : (TL s + BitVec.ofNat 64 0).toNat = p.length := by rw [BitVec.add_zero]; exact hpl
  obtain ⟨sr₆, dd₆⟩ := post iv a p sr₅ hal hpl'
  rw [hX₅] at sr₆ dd₆
  rw [BitVec.add_zero] at dd₆
  exact ⟨sr₆, dd₆⟩

theorem hd_wp (htl : (TL s).toNat + Hd s < 2 ^ 64) {st : State} (h : HD s st) :
    WP isa (.block headDone) st (Mid s (Hd s)) := by
  obtain ⟨cs₆, sp₆, rd₆, wr₆, f₆, k₆, h72₆, sem₆, mx₆⟩ := h
  have hHL : Hd s ≤ L s := Nat.min_le_right _ _
  exact WP.mono_mx (by decide) (headDone_ok hp sp₆ rd₆ wr₆ f₆ k₆ h72₆) fun _ ⟨cs₇, k₇, f₇, rd₇, wr₇⟩ mx₇ =>
    ⟨hHL, htl, by rw [cs₇ _ (by decide), sp₆], fun r hr => by rw [cs₇ r hr, cs₆ r hr], rd₇.trans rd₆,
      wr₇.trans wr₆, k₇, f₆.trans (frame_kR' f₇), sem₆.kR' hp f₇ hHL, mx₇.trans mx₆⟩

/-- `head`, from `Mid s 0` with `work` in `r11` and the text so far in
`r8`: some bytes done. -/
theorem head_ok (E : EncFn M) {st : State} (h : HB s st) :
    WP isa (head E.fn) st fun st' => ∃ o, Mid s o st' := by
  unfold head
  refine WP.seq (WP.mono (hl_wp hp h) fun s₁ ⟨B₁, ax₁, z₁⟩ => ?_)
  refine WP.ite (decide (Hd s = 0)) (by simp only [eval, z₁]) (fun _ => WP.block_nil ⟨0, B₁.1⟩) (fun e₁ => ?_)
  have hk0 : Hd s ≠ 0 := by simpa using e₁
  refine WP.seq (WP.mono (ho_wp ⟨B₁, ax₁⟩) fun s₂ ⟨B₂, cf₂⟩ => ?_)
  refine WP.ite (decide (2 ^ 64 ≤ (TL s).toNat + Hd s)) (by simp only [eval, cf₂])
    (fun _ => WP.block_nil ⟨0, B₂.1.1⟩) (fun e₂ => ?_)
  have htl : (TL s).toNat + Hd s < 2 ^ 64 := by simpa using e₂
  exact WP.seq (WP.mono (hp_wp hp B₂) fun _ h₃ => WP.seq (WP.mono (hc_wp hp hk0 h₃) fun _ h₄ =>
    WP.seq (WP.mono (ha_wp hp h₄) fun _ h₅ => WP.seq (WP.mono (hcall_wp hp E h₅) fun _ h₆ =>
      WP.mono (hd_wp hp htl h₆) fun _ h₇ => ⟨Hd s, h₇⟩))))

end

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-! ### `AesGcm.X86_64.StreamTo.Blocks`, which this module and modules that import it used -/

section

/-!
# AES-GCM streaming encryption out of place, x86-64: the whole blocks

Untrusted: everything here is checked by Lean. `blocks` from `Mid s o`: if
the text so far and the `o` bytes done end a block, and are not empty or
follow additional data of whole blocks (`Sel`, the length the code tests),
and there are `q ≥ 1` whole blocks of plaintext left (and the text so far,
the bytes done and they do not exceed 2⁶⁴ bytes), the call of
`vg_aes_gcm_encrypt_blocks_to` leaves `Mid s (o + 16 q)`
(`call_mid`, from `Proof.Gcm.streamRepr_blocksTo`); otherwise nothing is
done (`blocks_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt StreamRepr gctr inc32 j0)

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The regions the call writes are apart from the slots kept. -/
theorem kR'_blk {o q : Nat} (hq : o + 16 * q ≤ L s) : ∀ r ∈ blkWr s o q ++ [tR s], (kR' s).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact (hp.st_w.symm.sub_left kR'_sub).sub_right ctr_sub
  · exact (hp.st_w.symm.sub_left kR'_sub).sub_right y_sub
  · exact (hp.d_w.symm.sub_left kR'_sub).sub_right (dst_sub (s := s) hq)
  · exact kR'_scR
  · exact hp.b_w.symm.sub_left kR'_sub

omit hp in
/-- The regions the call writes are among those the code may write. -/
theorem blk_wR {o q : Nat} (hq : o + 16 * q ≤ L s) {m m' : Mem} (hf : Frame (blkWr s o q ++ [tR s]) m m') :
    Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl
    · exact ⟨stR s, by simp, ctr_sub⟩
    · exact ⟨stR s, by simp, y_sub⟩
    · exact ⟨dR s, by simp, dst_sub (s := s) hq⟩
    · exact ⟨wkR s, by simp, scR_sub⟩
    · exact ⟨tR s, by simp, fun _ h => h⟩

/-- `J₀`, the first 16 bytes of the state, is apart from what the call writes. -/
theorem j0_blk {o q : Nat} (hq : o + 16 * q ≤ L s) :
    ∀ r ∈ blkWr s o q ++ [tR s], (⟨St s, 16⟩ : Region).Disjoint r := by
  obtain hs : Region.Sub ⟨St s, 16⟩ (stR s) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact Offset.base_disjoint _ (by decide) (by have := hp.w_st; omega_arith)
  · exact Offset.base_disjoint _ (by decide) (by have := hp.w_st; omega_arith)
  · exact (hp.st_d.sub_left hs).sub_right (dst_sub (s := s) hq)
  · exact (hp.st_w.sub_left hs).sub_right scR_sub
  · exact hp.b_st.symm.sub_left hs

/-- The first `o` bytes of the output are apart from what the call writes
after them. -/
theorem pre_blk {o q : Nat} (hq : o + 16 * q ≤ L s) :
    ∀ r ∈ blkWr s o q ++ [tR s], (⟨Dst s, o⟩ : Region).Disjoint r := by
  obtain hs : Region.Sub ⟨Dst s, o⟩ (dR s) := Region.sub_prefix (by omega_arith)
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact (hp.st_d.symm.sub_left hs).sub_right ctr_sub
  · exact (hp.st_d.symm.sub_left hs).sub_right y_sub
  · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega_arith)
  · exact (hp.d_w.sub_left hs).sub_right scR_sub
  · exact hp.b_d.symm.sub_left hs

omit hp in
/-- The length whose remainder modulo 16 decides whether the whole blocks
can be taken: `aad_len` after no text, and the text so far and the `o`
bytes done otherwise. -/
abbrev Sel (s : State) (o : Nat) : BitVec 64 :=
  if TL s + BitVec.ofNat 64 o = 0 then AL s else TL s + BitVec.ofNat 64 o

omit hp in
/-- Whether `Sel` is a multiple of 16: the text so far and the bytes done
end a block, and are not empty or follow additional data of whole blocks. -/
theorem sel_mod {s : State} {o : Nat} (h : (Sel s o).toNat % 16 = 0) :
    (TL s + BitVec.ofNat 64 o).toNat % 16 = 0 ∧ (TL s + BitVec.ofNat 64 o ≠ 0 ∨ (AL s).toNat % 16 = 0) := by
  by_cases ht : TL s + BitVec.ofNat 64 o = 0
  · simp only [Sel, ht, ite_true] at h; exact ⟨by rw [ht]; rfl, Or.inr h⟩
  · simp only [Sel, ht, ite_false] at h; exact ⟨h, Or.inl ht⟩

omit hp in
/-- The text so far and the `o` bytes done, exact in 64 bits. -/
theorem tl_add {s : State} {o : Nat} (h : (TL s).toNat + o < 2 ^ 64) :
    (TL s + BitVec.ofNat 64 o).toNat = (TL s).toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt h]

/-- What the call of the whole blocks leaves: `Mid s (o + 16 q)`, from the
state `st₄` it starts from (with `o` bytes done and the bytes done after the
call kept). -/
theorem call_mid {o q : Nat} (hq0 : q ≠ 0) (hq : o + 16 * q ≤ L s) (htl : (TL s).toNat + (o + 16 * q) < 2 ^ 64)
    (ht0 : TL s + BitVec.ofNat 64 o ≠ 0 ∨ (AL s).toNat % 16 = 0) (ht16 : ((TL s).toNat + o) % 16 = 0)
    {st₄ st' : State}
    (f₄ : Frame (wR s ++ [tR s]) s.mem st₄.mem) (sem₄ : Sem s o st₄.mem) (hk₄ : Kept s (o + 16 * q) st₄.mem)
    (hsp₄ : st₄.gpr .rsp = SP s) (hcs₄ : ∀ r ∈ calleeSaved, st₄.gpr r = s.gpr r) (hrd₄ : st₄.rd = s.rd)
    (hwr₄ : st₄.wr = s.wr) (hmx : st'.mxcsr = s.mxcsr)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st₄.gpr r) (hrd : st'.rd = st₄.rd) (hwr : st'.wr = st₄.wr)
    (hf : Frame (blkWr s o q ++ [tR s]) st₄.mem st'.mem)
    (o₁ : blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q =
      Spec.Gcm.ctr32 (ciph s) (blockAt st₄.mem (St s + BitVec.ofNat 64 48))
        (blocksAt st₄.mem (Src s + BitVec.ofNat 64 o) q))
    (o₂ : blockAt st'.mem (St s + BitVec.ofNat 64 48) =
      Nat.repeat inc32 q (blockAt st₄.mem (St s + BitVec.ofNat 64 48)))
    (o₃ : blockAt st'.mem (St s + BitVec.ofNat 64 16) =
      Spec.Gcm.ghashFrom (hk s) (blockAt st₄.mem (St s + BitVec.ofNat 64 16))
        (blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q)) :
    Mid s (o + 16 * q) st' := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  obtain f' : Frame (wR s ++ [tR s]) s.mem st'.mem := f₄.trans (blk_wR (s := s) hq hf)
  refine ⟨hq, htl, by rw [hcs _ (by decide), hsp₄], fun r hr => by rw [hcs r hr, hcs₄ r hr],
    by rw [hrd, hrd₄], by rw [hwr, hwr₄], hk₄.frame hf (kR'_blk hp hq), f',
    fun iv a p hr hal hpl => ?_, hmx⟩
  -- The state before the call.
  obtain ⟨hr₄, dd₄⟩ := sem₄ iv a p hr hal hpl
  obtain hX : (p ++ pt s o).length = (TL s).toNat + o := by rw [List.length_append, length_bytesAt, hpl]
  obtain hc : gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o) ≠ [] ∨ a.length % 16 = 0 := by
    rcases ht0 with ht0 | ha
    · refine Or.inl fun e => ?_
      have := congrArg List.length e
      rw [Proof.Gcm.length_gctr, hX] at this; simp at this
      exact ht0 (by apply BitVec.eq_of_toNat_eq; rw [tl_add (by omega_arith), this.1, this.2]; rfl)
    · rw [hal, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)] at ha
      exact Or.inr ha
  obtain hc0 : (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o)).length % 16 = 0 := by
    rw [Proof.Gcm.length_gctr, hX]; exact ht16
  obtain ⟨e₁, hr'⟩ := Proof.Gcm.streamRepr_blocksTo hr₄ hc hc0 hq0
    (blockAt_frame hf (j0_blk hp hq)) o₁ o₂ o₃
  obtain hsub : Region.Sub ⟨Src s + BitVec.ofNat 64 o, 16 * q⟩ (srcR s) := Offset.sub_base _ (by omega_arith)
  obtain hpt : bytesAt st₄.mem (Src s + BitVec.ofNat 64 o) (16 * q) = bytesAt s.mem (Src s + BitVec.ofNat 64 o) (16 * q) :=
    bytesAt_frame f₄ (fun r hr => (r_disj hp r hr).sub_left hsub) (by omega_arith)
  rw [hpt, Proof.Gcm.length_gctr] at e₁
  obtain hP : p ++ pt s (o + 16 * q) = p ++ pt s o ++ bytesAt s.mem (Src s + BitVec.ofNat 64 o) (16 * q) := by
    rw [List.append_assoc, ← bytesAt_add]
  obtain hg : gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s (o + 16 * q)) =
      gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o) ++ bytesAt st'.mem (Dst s + BitVec.ofNat 64 o) (16 * q) := by
    rw [hP, Proof.Gcm.gctr_append, e₁]
  refine ⟨by rw [hg]; exact hr', ?_⟩
  obtain hD : bytesAt st'.mem (Dst s) o = bytesAt st₄.mem (Dst s) o :=
    bytesAt_frame hf (pre_blk hp hq) (by omega_arith)
  rw [hg, bytesAt_add, hD, dd₄, List.drop_append_of_le_length (by rw [Proof.Gcm.length_gctr]; simp)]

/-- `blocks`, from `Mid s o`: some bytes done. -/
theorem blocks_ok (T : BlkToFn M) {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (blocks T.fn) st fun st' => ∃ o', Mid s o' st' := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  have htl := h.tl
  unfold blocks
  refine WP.seq (WP.mono_mx (by decide) (blocksLoad_ok hp h) fun s₀ ⟨h11, hcx, h8, g₀, m₀, rd₀, wr₀⟩ mx_s₀ => ?_)
  obtain M₀ : Mid s o s₀ := h.regs m₀ (fun r hr => g₀ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₀ wr₀ mx_s₀
  refine WP.seq (WP.mono_mx (by decide) hd1_ok fun s₁ ⟨ax₁, z₁, g₁, m₁, rd₁, wr₁⟩ mx_s₁ => ?_)
  obtain M₁ : Mid s o s₁ := M₀.regs m₁ (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr)) rd₁ wr₁ mx_s₁
  -- `rax`: `aad_len` after no text, and the text so far and the bytes done otherwise.
  obtain hsel : WP isa (.ite .e (.block [.mov .rax (.reg .rcx)]) (.block [])) s₁ fun s₂ =>
      s₂.gpr .rax = Sel s o ∧ (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
    refine WP.ite (s₀.gpr .r8 == 0) (by simp only [eval, z₁]) (fun e => WP.mono mvc_ok fun _ ⟨ax, g, m, rd, wr⟩ =>
      ⟨by
        obtain hz : TL s + BitVec.ofNat 64 o = 0 := by rw [← h8]; simpa using e
        rw [ax, g₁ _ (by decide), hcx]; simp only [Sel, hz, ite_true], g, m, rd, wr⟩)
      (fun e => WP.block_nil ⟨by
        obtain hz : TL s + BitVec.ofNat 64 o ≠ 0 := by rw [← h8]; simpa using e
        rw [ax₁, h8]; simp only [Sel, hz, ite_false], fun _ _ => rfl, rfl, rfl, rfl⟩)
  refine WP.seq (WP.mono_mx (by decide) hsel fun s₁' ⟨ax₁', g₁', m₁', rd₁', wr₁'⟩ mx_s₁' => ?_)
  obtain M₁' : Mid s o s₁' := M₁.regs m₁' (fun r hr => g₁' r (by rintro rfl; simp [calleeSaved] at hr)) rd₁' wr₁' mx_s₁'
  refine WP.seq (WP.mono_mx (by decide) (hd2_ok (T := Sel s o) ax₁') fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ mx_s₂ => ?_)
  obtain M₂ : Mid s o s₂ := M₁'.regs m₂ (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂ mx_s₂
  refine WP.ite (!(BitVec.ofNat 64 ((Sel s o).toNat % 16) == 0)) (by simp only [eval, z₂, Option.map_some])
    (fun _ => WP.block_nil ⟨o, M₂⟩) (fun e₂ => ?_)
  obtain ⟨ht16, ht0⟩ := sel_mod (s := s) (o := o) (by
    simp only [Bool.not_eq_false', beq_iff_eq] at e₂
    have := congrArg BitVec.toNat e₂
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this)
  rw [tl_add htl] at ht16
  obtain h11₂ : s₂.gpr .r11 = W s := by rw [g₂ _ (by decide), g₁' _ (by decide), g₁ _ (by decide), h11]
  refine WP.seq (WP.mono_mx (by decide) (blocksCount_ok hp h11₂ M₂.kept ho M₂.rd M₂.wr) fun s₃ ⟨ax₃, z₃, g₃, m₃, rd₃, wr₃⟩ mx_s₃ => ?_)
  obtain M₃ : Mid s o s₃ := M₂.regs m₃ (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃ mx_s₃
  refine WP.ite (decide ((L s - o) / 16 = 0)) (by simp only [eval, z₃]) (fun _ => WP.block_nil ⟨o, M₃⟩)
    (fun e₃ => ?_)
  obtain hq0 : (L s - o) / 16 ≠ 0 := by simpa using e₃
  obtain h8₃ : s₃.gpr .r8 = TL s + BitVec.ofNat 64 o := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁' _ (by decide), g₁ _ (by decide), h8]
  refine WP.seq (WP.mono_mx (by decide) (len_ok ax₃ h8₃) fun s₄ ⟨r9₄, ax₄, cf₄, g₄, m₄, rd₄, wr₄⟩ mx_s₄ => ?_)
  obtain M₄ : Mid s o s₄ := M₃.regs m₄ (fun r hr => g₄ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₄ wr₄ mx_s₄
  obtain h16 : (BitVec.ofNat 64 (16 * ((L s - o) / 16))).toNat = 16 * ((L s - o) / 16) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  rw [h16, tl_add htl] at cf₄
  refine WP.ite (decide (2 ^ 64 ≤ (TL s).toNat + o + 16 * ((L s - o) / 16))) (by simp only [eval, cf₄])
    (fun _ => WP.block_nil ⟨o, M₄⟩) (fun e₄ => ?_)
  obtain htl' : (TL s).toNat + (o + 16 * ((L s - o) / 16)) < 2 ^ 64 := by simp at e₄; omega_arith
  obtain h11₄ : s₄.gpr .r11 = W s := by
    rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide), h11₂]
  refine WP.seq (WP.mono_mx (by decide) (blocksArgs_ok hp h11₄ ax₄ M₄.kept M₄.rd M₄.wr)
    fun s₅ ⟨di, si, dx, cx, r8₅, r10₅, ax₅, g₅, k₅, f₅, rd₅, wr₅⟩ mx₅ => ?_)
  obtain hq : o + 16 * ((L s - o) / 16) ≤ L s := by omega_arith
  obtain sp₅ : s₅.gpr .rsp = SP s := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), M₄.rsp]
  obtain r9₅ : s₅.gpr .r9 = BitVec.ofNat 64 ((L s - o) / 16) := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9₄]
  have si₅ : s₅.gpr .rsi = s.gpr .rsi := si
  refine WP.mono_mx (call_frame_mx T.mx) (blkCall_ok hp T hq sp₅ (rd₅.trans M₄.rd) (wr₅.trans M₄.wr)
    (M₄.frame.trans (frame_kR' f₅)) di si₅ dx cx r8₅ r9₅ r10₅ ax₅)
    fun s₆ ⟨cs₆, rd₆, wr₆, f₆, o₁, o₂, o₃⟩ mx₆ => ⟨o + 16 * ((L s - o) / 16), ?_⟩
  obtain cs₅ : ∀ r ∈ calleeSaved, s₅.gpr r = s.gpr r := fun r hr => by
    rw [g₅ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr), M₄.saved r hr]
  exact call_mid hp hq0 hq htl' ht0 ht16 (M₄.frame.trans (frame_kR' f₅)) (M₄.sem.kR' hp f₅ ho) k₅
    sp₅ cs₅ (rd₅.trans M₄.rd) (wr₅.trans M₄.wr) (mx₆.trans (mx₅.trans M₄.mx)) cs₆ rd₆ wr₆ f₆ o₁ o₂ o₃

end

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-!
# AES-GCM streaming encryption out of place, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments go through the same pieces: each load of `work` from
the stack gives both the same pointer (`rel_w`), after which the taint
analysis checks the piece from it; every other value a piece branches on or
addresses memory with is the same in both runs by what correctness says of
each (`step`): the lengths, the bytes done and the pointers; and the calls
get the same public arguments.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-! ## Two runs, piece by piece -/

/-- A piece the taint analysis checks from registers that agree, with what
correctness says of each run after it. -/
theorem step {P : State → State → Prop} {c : Prog isa} {F₁ F₂ G₁ G₂ : State → Prop} (rs : List Reg)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (hF : ∀ s₁ s₂, P s₁ s₂ → F₁ s₁ ∧ F₂ s₂)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa P c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (rel_wp (rel_taint rs hag hc) hF hw₁ hw₂).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A fact the related states imply, for the rest of the proof. -/
theorem RelCT.of_imp {P Q : State → State → Prop} {c : Prog isa} (A : Prop) (hA : ∀ s₁ s₂, P s₁ s₂ → A)
    (h : A → RelCT isa P c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h (hA _ _ hp) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

theorem empty_check : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩

/-- Nothing, in two runs. -/
theorem skip_rel {P Q : State → State → Prop} (h : ∀ s₁ s₂, P s₁ s₂ → Q s₁ s₂) :
    RelCT isa P (.block []) Q :=
  (rel_wp (P := P) (F₁ := fun _ => True) (F₂ := fun _ => True) (G₁ := fun _ => True) (G₂ := fun _ => True)
    (rel_taint [] (fun _ _ _ r hr => by cases hr) empty_check) (fun _ _ _ => ⟨trivial, trivial⟩)
    (fun _ _ => WP.block_nil trivial) (fun _ _ => WP.block_nil trivial)).wpDep
    (F := fun σ s' => s' = σ) (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) |>.mono (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hσ, e₁, e₂⟩ => by rw [e₁, e₂]; exact h _ _ hσ

/-- `work`, loaded from the stack into `r11`. -/
theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 32))]) s fun s' =>
      s'.gpr .r11 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 ∧ ∀ r, r ≠ .r11 → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]

theorem loadW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 32))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- A block that first loads `work` into `r11`, from states that agree on
`rs` (with `rsp`) and hold the same pointer there, checked from `r11` and
`rs`. -/
theorem rel_w {P : State → State → Prop} {l₀ l : List Instr}
    (hl : l₀ = ([.mov .r11 (.mem (at_ .rsp 32))] : List Instr) ++ l) (rs : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 8)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (.r11 :: rs)) (.block l) hc).isSome = true) :
    RelCT isa P (.block l₀) fun _ _ => True := by
  subst hl
  have l₁ := RelCT.wpDep (rel_taint (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) loadW_check)
    (F := fun (σ s' : State) => s'.gpr .r11 = σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      ∀ r, r ≠ .r11 → s'.gpr r = σ.gpr r)
    fun s₁ s₂ h => ⟨loadW_ok (hS _ _ h).2.1, loadW_ok (hS _ _ h).2.2⟩
  refine rel_block_split (RelCT.seq l₁ (rel_taint (.r11 :: rs) (fun s₁ s₂ h r hr => ?_) hc))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ := h
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]; exact (hS _ _ hσ).1
  · by_cases hx : r = .r11
    · subst hx; rw [a₁, a₂]; exact (hS _ _ hσ).1
    · rw [b₁ r hx, b₂ r hx]; exact hag _ _ hσ r hr

/-! ## What each run holds -/

/-- `o` bytes done, `work` in `r11`, the text so far and the bytes done in `r8`. -/
def B0 (s : State) (o : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .r11 = W s ∧ st.gpr .r8 = TL s + BitVec.ofNat 64 o

/-- Before `blocks`' test: `B0`, with `aad_len` in `rcx`. -/
def B0c (s : State) (o : Nat) (st : State) : Prop := B0 s o st ∧ st.gpr .rcx = AL s

/-- `B0`, with `Sel` in `rax`. -/
def B1 (s : State) (o : Nat) (st : State) : Prop := B0 s o st ∧ st.gpr .rax = Sel s o

/-- Before the call of the whole blocks. -/
def C5 (s : State) (o q : Nat) (st : State) : Prop :=
  Frame (wR s ++ [tR s]) s.mem st.mem ∧ Sem s o st.mem ∧ Kept s (o + 16 * q) st.mem ∧ st.gpr .rsp = SP s ∧
    (∀ r ∈ calleeSaved, st.gpr r = s.gpr r) ∧ st.rd = s.rd ∧ st.wr = s.wr ∧
    st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s + BitVec.ofNat 64 48 ∧
    st.gpr .rcx = St s + BitVec.ofNat 64 16 ∧ st.gpr .r8 = Src s + BitVec.ofNat 64 o ∧
    st.gpr .r9 = BitVec.ofNat 64 q ∧ st.gpr .r10 = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .rax = W s + BitVec.ofNat 64 80 ∧ st.mxcsr = s.mxcsr

/-- Before the copy of the bytes left. -/
def R2 (s : State) (o : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .rsi = Src s + BitVec.ofNat 64 o ∧ st.gpr .rdi = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .rcx = BitVec.ofNat 64 (L s - o)

/-- Before a call of `vg_aes_gcm_stream_encrypt` on `n` bytes after `o`. -/
def R4 (s : State) (o n : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = TL s + BitVec.ofNat 64 o ∧ st.gpr .r9 = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .r10 = BitVec.ofNat 64 n

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem notCs {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem b0_wp {o : Nat} {st : State} (h : Mid s o st) : WP isa (.block blocksLoad) st (B0c s o) :=
  WP.mono_mx (by decide) (blocksLoad_ok hp h) fun _ ⟨r11, cx, r8, g, m, rd, wr⟩ mxw =>
    ⟨⟨h.regs m (fun r hr => g r (notCs hr).2.2.2.2.2.2.2.2 (notCs hr).2.1 (notCs hr).2.2.2.2.2.1 (notCs hr).1)
      rd wr mxw, r11, r8⟩, cx⟩

omit hp in
theorem b1_wp {o : Nat} {st : State} (h : B0c s o st) :
    WP isa (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) st fun st' =>
      B0c s o st' ∧ st'.gpr .rax = TL s + BitVec.ofNat 64 o ∧ st'.zf = some (TL s + BitVec.ofNat 64 o == 0) :=
  WP.mono_mx (by decide) hd1_ok fun _ ⟨ax, z, g, m, rd, wr⟩ mxw =>
    ⟨⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1) rd wr mxw, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, by rw [g _ (by decide), h.2]⟩, by rw [ax, h.1.2.2], by rw [z, h.1.2.2]⟩

omit hp in
/-- After no text, `aad_len` into `rax`. -/
theorem bsel_wp {o : Nat} {st : State} (h : B0c s o st) (hz : TL s + BitVec.ofNat 64 o = 0) :
    WP isa (.block [.mov .rax (.reg .rcx)]) st (B1 s o) :=
  WP.mono_mx (by decide) mvc_ok fun _ ⟨ax, g, m, rd, wr⟩ mxw =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1) rd wr mxw, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, by rw [ax, h.2]; simp only [Sel, hz, ite_true]⟩

omit hp in
/-- After some text, the text so far and the bytes done are in `rax` already. -/
theorem bsel_of {o : Nat} {st : State} (h : B0c s o st ∧ st.gpr .rax = TL s + BitVec.ofNat 64 o)
    (hz : TL s + BitVec.ofNat 64 o ≠ 0) : B1 s o st :=
  ⟨h.1.1, by rw [h.2]; simp only [Sel, hz, ite_false]⟩

omit hp in
theorem b2_wp {o : Nat} {st : State} (h : B1 s o st) :
    WP isa (.block [.alu .and .rax (imm 15)]) st fun st' =>
      B0 s o st' ∧ st'.zf = some (BitVec.ofNat 64 ((Sel s o).toNat % 16) == 0) :=
  WP.mono_mx (by decide) (hd2_ok h.2) fun _ ⟨z, g, m, rd, wr⟩ mxw =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1) rd wr mxw, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, z⟩

theorem b3_wp {o : Nat} {st : State} (h : B0 s o st) :
    WP isa (.block blocksCount) st
      fun st' => B0 s o st' ∧ st'.gpr .rax = BitVec.ofNat 64 ((L s - o) / 16) ∧
        st'.zf = some (decide ((L s - o) / 16 = 0)) :=
  WP.mono_mx (by decide) (blocksCount_ok hp h.2.1 h.1.kept h.1.o_le h.1.rd h.1.wr) fun _ ⟨ax, z, g, m, rd, wr⟩ mxw =>
    ⟨⟨h.1.regs m (fun r hr => g r (notCs hr).1 (notCs hr).2.1) rd wr mxw, by rw [g _ (by decide) (by decide), h.2.1],
      by rw [g _ (by decide) (by decide), h.2.2]⟩, ax, z⟩

omit hp in
theorem b4_wp {o : Nat} {st : State} (h : B0 s o st ∧ st.gpr .rax = BitVec.ofNat 64 ((L s - o) / 16)) :
    WP isa (.block blocksLen) st fun st' => B0 s o st' ∧ st'.gpr .r9 = BitVec.ofNat 64 ((L s - o) / 16) ∧
      st'.gpr .rax = BitVec.ofNat 64 (16 * ((L s - o) / 16)) ∧
      st'.cf = some (decide (2 ^ 64 ≤ (TL s).toNat + o + 16 * ((L s - o) / 16))) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have h16 : (BitVec.ofNat 64 (16 * ((L s - o) / 16))).toNat = 16 * ((L s - o) / 16) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hL])
  exact WP.mono_mx (by decide) (len_ok h.2 h.1.2.2) fun _ ⟨r9, ax, cf, g, m, rd, wr⟩ mxw =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1 (notCs hr).2.2.2.2.2.2.1 (notCs hr).2.1) rd wr mxw,
      by rw [g _ (by decide) (by decide) (by decide), h.1.2.1], by rw [g _ (by decide) (by decide) (by decide), h.1.2.2]⟩,
      r9, ax, by rw [cf, h16, tl_add h.1.1.tl]⟩

theorem b5_wp {o q : Nat} {st : State}
    (h : B0 s o st ∧ st.gpr .r9 = BitVec.ofNat 64 q ∧ st.gpr .rax = BitVec.ofNat 64 (16 * q)) :
    WP isa (.block blocksArgs) st (C5 s o q) :=
  WP.mono_mx (by decide) (blocksArgs_ok hp h.1.2.1 h.2.2 h.1.1.kept h.1.1.rd h.1.1.wr)
    fun _ ⟨di, si, dx, cx, r8, r10, ax, g, k, f, rd, wr⟩ mxw =>
      ⟨h.1.1.frame.trans (frame_kR' f), h.1.1.sem.kR' hp f h.1.1.o_le, k,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.rsp],
        fun r hr => by
          have n := notCs hr
          rw [g r n.2.2.2.2.1 n.2.2.2.1 n.2.2.1 n.2.1 n.2.2.2.2.2.1 n.2.2.2.2.2.2.2.1 n.1, h.1.1.saved r hr],
        rd.trans h.1.1.rd, wr.trans h.1.1.wr, di, si, dx, cx, r8,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.2.1],
        r10, ax, mxw.trans h.1.1.mx⟩

theorem b6_wp (T : BlkToFn M) {o q : Nat} (hq0 : q ≠ 0) (hq : o + 16 * q ≤ L s)
    (htl : (TL s).toNat + (o + 16 * q) < 2 ^ 64) (ht0 : TL s + BitVec.ofNat 64 o ≠ 0 ∨ (AL s).toNat % 16 = 0)
    (ht16 : ((TL s).toNat + o) % 16 = 0) {st : State} (h : C5 s o q st) :
    WP isa (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st (Mid s (o + 16 * q)) := by
  obtain ⟨f, sem, k, sp, cs, rd, wr, di, si, dx, cx, r8, r9, r10, ax, mx⟩ := h
  exact WP.mono_mx (call_frame_mx T.mx) (blkCall_ok hp T hq sp rd wr f di si dx cx r8 r9 r10 ax)
    fun _ ⟨cs₆, rd₆, wr₆, f₆, o₁, o₂, o₃⟩ mx₆ =>
    call_mid hp hq0 hq htl ht0 ht16 f sem k sp cs rd wr (mx₆.trans mx) cs₆ rd₆ wr₆ f₆ o₁ o₂ o₃

theorem r1_wp {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]) st fun st' =>
      Mid s o st' ∧ st'.gpr .r11 = W s ∧ st'.gpr .rcx = BitVec.ofNat 64 (L s - o) ∧
      st'.gpr .rax = BitVec.ofNat 64 o ∧ st'.zf = some (decide (L s - o = 0)) :=
  WP.mono_mx (by decide) (restHead_ok hp h) fun _ ⟨r11, cx, ax, z, g, m, rd, wr⟩ mxw =>
    ⟨h.regs m (fun r hr => g r (notCs hr).2.2.2.2.2.2.2.2 (notCs hr).2.1 (notCs hr).1) rd wr mxw, r11, cx, ax, z⟩

theorem r2_wp {o : Nat} {st : State}
    (h : Mid s o st ∧ st.gpr .r11 = W s ∧ st.gpr .rcx = BitVec.ofNat 64 (L s - o) ∧ st.gpr .rax = BitVec.ofNat 64 o) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax), .mov .rdi (.mem (at_ .r11 wDst)),
      .alu .add .rdi (.reg .rax)]) st (R2 s o) :=
  WP.mono_mx (by decide) (restPtrs_ok hp h.1 h.2.1 h.2.2.2) fun _ ⟨si, di, g, m, rd, wr⟩ mxw =>
    ⟨h.1.regs m (fun r hr => g r (notCs hr).2.2.2.1 (notCs hr).2.2.2.2.1) rd wr mxw, si, di,
      by rw [g _ (by decide) (by decide), h.2.2.1]⟩

theorem r3_wp {o : Nat} (ho : o < L s) {st : State} (h : R2 s o st) : WP isa copyLoop st (Mid s o) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  obtain ⟨M₂, si, di, cx⟩ := h
  have ds := dq_sub (s := s) (o := o) (n := L s - o) (by omega_using [ho])
  have ss : Region.Sub ⟨Src s + BitVec.ofNat 64 o, L s - o⟩ (srcR s) := Offset.sub_base _ (by omega_using [ho])
  have cp : CopyPre st (Src s + BitVec.ofNat 64 o) (Dst s + BitVec.ofNat 64 o) (L s - o) :=
    ⟨si, di, cx, by omega_using [ho], by omega_using [hL],
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.rd, M₂.wr, hp.rd]; simp) (by omega_using [ho]) (by omega_using [ho, hL]),
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.wr, hp.wr]; simp) (by omega_using [ho]) (by omega_using [ho, hL]),
      (hp.r_d.sub_left ss).sub_right ds⟩
  exact WP.mono_mx (by decide) (copyLoopL_ok st cp) fun _ ⟨m₃, g₃, rd₃, wr₃⟩ mxw =>
    M₂.copy hp (n := L s - o) (by omega_using [ho]) (by rw [m₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _))
      (fun r hr => g₃ r (notCs hr).1 (notCs hr).2.2.2.2.2.2.2.1) rd₃ wr₃ mxw

theorem r4_wp {o : Nat} {st : State} (h : Mid s o st) : WP isa (.block restArgs) st (R4 s o (L s - o)) :=
  WP.mono_mx (by decide) (restArgs_ok hp h) fun _ ⟨di, si, dx, cx, r8, r9, r10, cs, m, rd, wr⟩ mxw =>
    ⟨h.regs m cs rd wr mxw, di, si, dx, cx, r8, r9, r10⟩

end

/-! ## Two runs -/

/-- What two entry states with the same public arguments share. -/
structure Pub (s₀ s₀' : State) : Prop where
  k : K s₀' = K s₀
  rsi : s₀'.gpr .rsi = s₀.gpr .rsi
  st : St s₀' = St s₀
  al : AL s₀' = AL s₀
  tl : TL s₀' = TL s₀
  src : Src s₀' = Src s₀
  sp : SP s₀' = SP s₀
  len : stackArg s₀' 0 = stackArg s₀ 0
  dst : Dst s₀' = Dst s₀
  w : W s₀' = W s₀
  mx : s₀'.mxcsr = s₀.mxcsr

theorem Pub.of {s₀ s₀' : State} (h : Proof.AesGcm.streamToPub s₀ s₀') : Pub s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.2.2.2.2.2.symm⟩

theorem Pub.eL {s₀ s₀' : State} (pb : Pub s₀ s₀') : L s₀' = L s₀ := by simp only [L, pb.len]

theorem Pub.eHd {s₀ s₀' : State} (pb : Pub s₀ s₀') : Hd s₀' = Hd s₀ := by simp only [Hd, pb.tl, pb.eL]

/-- The registers of the arguments, which the entry keeps. -/
def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem entry_check : ∃ hc, (taint.check (Taint.ofRegs (.r11 :: args)) (.block entry.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hlen_check : ∃ hc, (taint.check (Taint.ofRegs [.r8, .r11]) (.block headLen) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hover_check : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r8]) (.block headOver) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hptrs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rax]) (.block headPtrs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hargs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block headArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hdone_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block headDone.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem bload_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block blocksLoad.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hd1_check : ∃ hc, (taint.check (Taint.ofRegs [.r8])
    (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem mvc_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx]) (.block [.mov .rax (.reg .rcx)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem and_check : ∃ hc, (taint.check (Taint.ofRegs [.rax]) (.block [.alu .and .rax (imm 15)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem bcount_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block blocksCount) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem len_check : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r8]) (.block blocksLen) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem bargs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rax]) (.block blocksArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem rhead_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp])
    (.block [.mov .rcx (.mem (at_ .r11 wLen)), .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax),
      .alu .test .rcx (.reg .rcx)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem ptrs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rax])
    (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax), .mov .rdi (.mem (at_ .r11 wDst)),
      .alu .add .rdi (.reg .rax)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem copy_check : ∃ hc, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx]) copyLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem rargs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block restArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SP' M s₀) (hp' : SP' M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- `work` on the stack, in two runs through frames of the regions written. -/
theorem hW_of {s₁ s₂ : State} (sp₁ : s₁.gpr .rsp = SP s₀) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr)
    (f₁ : Frame (wR s₀ ++ [tR s₀]) s₀.mem s₁.mem) (sp₂ : s₂.gpr .rsp = SP s₀') (rd₂ : s₂.rd = s₀'.rd)
    (wr₂ : s₂.wr = s₀'.wr) (f₂ : Frame (wR s₀' ++ [tR s₀']) s₀'.mem s₂.mem) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 8 := by
  obtain ⟨i₁, w₁⟩ := w_stack' hp sp₁ rd₁ wr₁ f₁
  obtain ⟨i₂, w₂⟩ := w_stack' hp' sp₂ rd₂ wr₂ f₂
  exact ⟨by rw [w₁, w₂, pb.w], i₁, i₂⟩

/-- `work` on the stack, in two runs at `Mid`. -/
theorem mid_hW {o o' : Nat} {s₁ s₂ : State} (h₁ : Mid s₀ o s₁) (h₂ : Mid s₀' o' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 8 :=
  hW_of hp hp' pb h₁.rsp h₁.rd h₁.wr h₁.frame h₂.rsp h₂.rd h₂.wr h₂.frame

/-- The entry, in two runs. -/
theorem entry_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ =>
    HB s₀ s₁ ∧ HB s₀' s₂ := by
  have ea : ∀ r ∈ args, s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pb.k.symm, pb.rsi.symm, pb.st.symm, pb.al.symm, pb.tl.symm, pb.src.symm, pb.sp.symm]
  have toB0 : ∀ {s s₁ : State}, SP' M s → (s₁.gpr .r11 = W s ∧
      (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ Kept s 0 s₁.mem ∧ Frame [kR' s] s.mem s₁.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) → s₁.mxcsr = s.mxcsr → HB s s₁ := fun hp ⟨h11, hg, hk, hf, hrd, hwr⟩ hmx =>
    ⟨mid_entry hp (hg _ (by decide) (by decide) (by decide)) (fun r hr => hg r (notCs hr).2.2.2.2.2.2.2.2
      (notCs hr).1 (notCs hr).2.2.2.2.2.2.2.1) hk hf hrd hwr hmx, h11, hg _ (by decide) (by decide) (by decide)⟩
  refine (rel_wp (rel_w (l₀ := entry) (l := entry.tail) rfl args (by simp [args])
    (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ea) (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pb.w.symm, a_in hp (i := 3) (by decide), a_in hp' (i := 3) (by decide)⟩) entry_check)
    (fun _ _ h => h) (G₁ := HB s₀) (G₂ := HB s₀')
    (fun s h => by subst h; exact WP.mono_mx (by decide) (entry_ok hp) fun _ h hm => toB0 hp h hm)
    (fun s h => by subst h; exact WP.mono_mx (by decide) (entry_ok hp') fun _ h hm => toB0 hp' h hm)).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- The call of `n` bytes after `o`, in two runs. -/
theorem encCall_rel (E : EncFn M) {o n : Nat} (hn : o + n ≤ L s₀) :
    RelCT isa (fun s₁ s₂ => R4 s₀ o n s₁ ∧ R4 s₀' o n s₂)
      (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) fun _ _ => True := by
  have hn' : o + n ≤ L s₀' := by rw [pb.eL]; exact hn
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp, pb.sp])
    (RelCT.callEx (k := encK M) E.ok E.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, h, ha, hb⟩ := hab
  obtain ⟨⟨M₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁⟩, ⟨M₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁, a₁⟩ := encEntry hp hn M₁.rsp M₁.rd M₁.wr M₁.frame di₁ si₁ dx₁ r9₁ r10₁
  obtain ⟨p₂, c₂, w₂, a₂⟩ := encEntry hp' hn' M₂.rsp M₂.rd M₂.wr M₂.frame di₂ si₂ dx₂ r9₂ r10₂
  subst ha hb
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [pushed_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.sp]⟩
  have g : ∀ {t : State} {r : Reg} (rd wr : List Region), r ≠ .rsp →
      ((pushed [.r10] t).callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun _ _ h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h, pushed_gpr _ _ h]
  simp only [encK, encCallPub, Proof.AesGcm.arg, a₁, a₂, g _ _ (by decide : Reg.rdi ≠ .rsp),
    g _ _ (by decide : Reg.rsi ≠ .rsp), g _ _ (by decide : Reg.rdx ≠ .rsp), g _ _ (by decide : Reg.rcx ≠ .rsp),
    g _ _ (by decide : Reg.r8 ≠ .rsp), g _ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂,
    r8₁, r8₂, r9₁, r9₂, State.withRegions_gpr, State.callEntry_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.k, pb.rsi,
    pb.st, pb.al, pb.tl, pb.sp, pb.dst, pb.eL, State.withRegions_mxcsr, State.callEntry_mxcsr, pushed_mxcsr,
    M₁.mx, M₂.mx, pb.mx, and_self]

/-- `head`, in two runs: the same bytes done. -/
theorem head_rel (E : EncFn M) :
    RelCT isa (fun s₁ s₂ => HB s₀ s₁ ∧ HB s₀' s₂) (head E.fn) fun s₁ s₂ => ∃ o, Mid s₀ o s₁ ∧ Mid s₀' o s₂ := by
  have hL : L s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  have eHd := pb.eHd
  unfold head
  refine RelCT.seq (step [.r8, .r11] hlen_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.2.2, h.2.2.2, pb.tl]
      · rw [h.1.2.1, h.2.2.1, pb.w])
    (fun _ _ h => h) (fun _ => hl_wp hp) (fun _ => hl_wp hp')) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, eHd])
    (skip_rel fun _ _ h => ⟨0, h.1.1.1.1, h.1.2.1.1⟩) ?_
  refine RelCT.of_imp (Hd s₀ ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hk0 => ?_
  refine RelCT.seq (step [.rax, .r8] hover_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.2.1, h.1.2.2.1, eHd]
      · rw [h.1.1.1.2.2, h.1.2.1.2.2, pb.tl])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1⟩, ⟨h.1.2.1, h.1.2.2.1⟩⟩) (fun _ => ho_wp) (fun _ => ho_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2, h.2.2, eHd, pb.tl])
    (skip_rel fun _ _ h => ⟨0, h.1.1.1.1.1, h.1.2.1.1.1⟩) ?_
  refine RelCT.of_imp ((TL s₀).toNat + Hd s₀ < 2 ^ 64) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2] at e; simpa using e) fun htl => ?_
  refine RelCT.seq (step [.r11, .rax] hptrs_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.1.1.2.1, h.1.2.1.1.2.1, pb.w]
      · rw [h.1.1.1.2, h.1.2.1.2, eHd])
    (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ => hp_wp hp) (fun _ => hp_wp hp')) ?_
  refine RelCT.seq (step [.rsi, .rdi, .rcx] copy_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.2.1, h.2.2.1, pb.src]
      · rw [h.1.2.2.1, h.2.2.2.1, pb.dst]
      · rw [h.1.2.2.2.1, h.2.2.2.2.1, eHd])
    (fun _ _ h => h) (fun _ => hc_wp hp hk0) (fun _ => hc_wp hp' (by rw [eHd]; exact hk0))) ?_
  refine RelCT.seq ((rel_wp (rel_w (l₀ := headArgs) (l := headArgs.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.rsp, h.2.1.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1.1 h.2.1) hargs_check)
    (fun _ _ h => h) (fun _ => ha_wp hp) (fun _ => ha_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.seq ((rel_wp ((encCall_rel hp hp' pb E (o := 0) (n := Hd s₀)
      (by have : Hd s₀ ≤ L s₀ := Nat.min_le_right _ _; omega_using [this])).mono
      (fun _ _ h => ⟨⟨h.1.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
        h.1.2.2.2.2.2.2.1, h.1.2.2.2.2.2.2.2⟩, ⟨h.2.1.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
        h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2.2.2, eHd]⟩⟩) fun _ _ h => h)
    (fun _ _ h => h) (fun _ => hcall_wp hp E) (fun _ => hcall_wp hp' E)).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine ((rel_wp (rel_w (l₀ := headDone) (l := headDone.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.sp])
      (fun _ _ h => hW_of hp hp' pb h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
        h.2.2.2.2.2.1) hdone_check)
    (fun _ _ h => h) (fun _ => hd_wp hp htl) (fun _ => hd_wp hp' (by rw [pb.tl, eHd]; exact htl))).mono
    (fun _ _ h => h) fun _ _ h => ⟨Hd s₀, h.2.1, eHd ▸ h.2.2⟩)

/-- The call of the whole blocks, in two runs. -/
theorem blkCall_rel (T : BlkToFn M) {o q : Nat} (hq : o + 16 * q ≤ L s₀) :
    RelCT isa (fun s₁ s₂ => C5 s₀ o q s₁ ∧ C5 s₀' o q s₂)
      (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hq' : o + 16 * q ≤ L s₀' := by rw [pb.eL]; exact hq
  refine RelCT.frame (fun _ _ h => by rw [h.1.2.2.2.1, h.2.2.2.2.1, pb.sp])
    (RelCT.callEx (k := Proof.AesGcm.encryptBlocksToX86_64M M) T.ok T.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, h, ha, hb⟩ := hab
  obtain ⟨⟨f₁, -, -, sp₁, -, rd₁, wr₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁, ax₁, -⟩,
    ⟨f₂, -, -, sp₂, -, rd₂, wr₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, ax₂, -⟩⟩ := h
  obtain ⟨p₁, c₁, w₁, a₀₁, a₁₁, a₂₁⟩ := blkEntry hp hq sp₁ rd₁ wr₁ f₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ r10₁ ax₁
  obtain ⟨p₂, c₂, w₂, a₀₂, a₁₂, a₂₂⟩ := blkEntry hp' hq' sp₂ rd₂ wr₂ f₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ r10₂ ax₂
  subst ha hb
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [pushed_rsp, pushed_rsp, sp₁, sp₂, pb.sp]⟩
  have g : ∀ {t : State} {r : Reg} (rd wr : List Region), r ≠ .rsp →
      ((pushed [.rax, .r9, .r10] t).callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun _ _ h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h, pushed_gpr _ _ h]
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPub, Proof.AesGcm.arg, a₀₁, a₁₁, a₂₁, a₀₂,
    a₁₂, a₂₂, g _ _ (by decide : Reg.rdi ≠ .rsp), g _ _ (by decide : Reg.rsi ≠ .rsp),
    g _ _ (by decide : Reg.rdx ≠ .rsp), g _ _ (by decide : Reg.rcx ≠ .rsp), g _ _ (by decide : Reg.r8 ≠ .rsp),
    g _ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, r8₁, r8₂, r9₁, r9₂,
    State.withRegions_gpr, State.callEntry_rsp, pushed_rsp, sp₁, sp₂, pb.k, pb.rsi, pb.st, pb.src, pb.sp, pb.dst, pb.w, and_self]

/-- `blocks`, in two runs with the same bytes done: the same bytes done. -/
theorem blocks_rel (T : BlkToFn M) {o : Nat} :
    RelCT isa (fun s₁ s₂ => Mid s₀ o s₁ ∧ Mid s₀' o s₂) (blocks T.fn) fun s₁ s₂ =>
      ∃ o', Mid s₀ o' s₁ ∧ Mid s₀' o' s₂ := by
  have hL : L s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  have none : ∀ {P : State → State → Prop}, (∀ s₁ s₂, P s₁ s₂ → B0 s₀ o s₁ ∧ B0 s₀' o s₂) →
      RelCT isa P (.block []) fun s₁ s₂ => ∃ o', Mid s₀ o' s₁ ∧ Mid s₀' o' s₂ :=
    fun h => skip_rel fun _ _ hP => ⟨o, (h _ _ hP).1.1, (h _ _ hP).2.1⟩
  have esel : Sel s₀' o = Sel s₀ o := by simp only [Sel, pb.tl, pb.al]
  unfold blocks
  refine RelCT.seq ((rel_wp (rel_w (l₀ := blocksLoad) (l := blocksLoad.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1 h.2) bload_check)
    (fun _ _ h => h) (fun _ => b0_wp hp) (fun _ => b0_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.seq (step [.r8] hd1_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.2.2, h.2.1.2.2, pb.tl])
    (fun _ _ h => h) (fun _ => b1_wp) (fun _ => b1_wp)) ?_
  -- `Sel` into `rax`.
  refine RelCT.seq (R := fun s₁ s₂ => B1 s₀ o s₁ ∧ B1 s₀' o s₂)
    (RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.tl]) ?_ ?_) ?_
  · refine RelCT.of_imp (TL s₀ + BitVec.ofNat 64 o = 0) (fun _ _ h => by
      have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hz => ?_
    exact step [.rcx] mvc_check (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.1.2, h.1.2.1.2, pb.al])
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ h => bsel_wp h hz) (fun _ h => bsel_wp h (by rw [pb.tl]; exact hz))
  · refine RelCT.of_imp (TL s₀ + BitVec.ofNat 64 o ≠ 0) (fun _ _ h => by
      have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hz => ?_
    exact skip_rel fun _ _ h => ⟨bsel_of ⟨h.1.1.1, h.1.1.2.1⟩ hz, bsel_of ⟨h.1.2.1, h.1.2.2.1⟩ (by rw [pb.tl]; exact hz)⟩
  refine RelCT.seq (step [.rax] and_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, esel])
    (fun _ _ h => h) (fun _ => b2_wp) (fun _ => b2_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2, h.2.2, esel]) (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((Sel s₀ o).toNat % 16 = 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2, Option.map_some, Option.some.injEq, Bool.not_eq_false',
      beq_iff_eq] at e
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])] at this) fun hsel => ?_
  obtain ⟨ht16, ht0⟩ := sel_mod hsel
  refine RelCT.seq (step [.r11] bcount_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.1.2.1, h.1.2.1.2.1, pb.w])
    (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ => b3_wp hp) (fun _ => b3_wp hp')) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.eL])
    (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((L s₀ - o) / 16 ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hq0 => ?_
  refine RelCT.seq (step [.rax, .r8] len_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.2.1, h.1.2.2.1, pb.eL]
      · rw [h.1.1.1.2.2, h.1.2.1.2.2, pb.tl])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1⟩, ⟨h.1.2.1, h.1.2.2.1⟩⟩) (fun _ => b4_wp) (fun _ => b4_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2.2, h.2.2.2.2, pb.tl, pb.eL])
    (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((TL s₀).toNat + (o + 16 * ((L s₀ - o) / 16)) < 2 ^ 64) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2.2] at e; simp at e; omega_using [e]) fun htl => ?_
  refine RelCT.of_imp (o ≤ L s₀ ∧ (TL s₀).toNat + o < 2 ^ 64) (fun _ _ h => ⟨h.1.1.1.1.o_le, h.1.1.1.1.tl⟩)
    fun ⟨ho, hto⟩ => ?_
  rw [tl_add hto] at ht16
  refine RelCT.seq (step [.r11, .rax] bargs_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.1.2.1, h.1.2.1.2.1, pb.w]
      · rw [h.1.1.2.2.1, h.1.2.2.2.1, pb.eL])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1⟩, ⟨h.1.2.1, by rw [h.1.2.2.1, pb.eL],
      by rw [h.1.2.2.2.1, pb.eL]⟩⟩)
    (fun _ => b5_wp hp (q := (L s₀ - o) / 16)) (fun _ => b5_wp hp' (q := (L s₀ - o) / 16))) ?_
  have hq : o + 16 * ((L s₀ - o) / 16) ≤ L s₀ := by omega_using [hq0]
  refine (rel_wp (blkCall_rel hp hp' pb T hq) (fun _ _ h => h)
    (fun _ => b6_wp hp T hq0 hq htl ht0 ht16) (fun _ => b6_wp hp' T hq0
      (by rw [pb.eL]; exact hq) (by rw [pb.tl]; exact htl) (by rw [pb.tl, pb.al]; exact ht0)
      (by rw [pb.tl]; exact ht16))).mono
    (fun _ _ h => h) fun _ _ h => ⟨o + 16 * ((L s₀ - o) / 16), h.2.1, h.2.2⟩

/-- `rest`, in two runs with the same bytes done. -/
theorem rest_rel (E : EncFn M) {o : Nat} :
    RelCT isa (fun s₁ s₂ => Mid s₀ o s₁ ∧ Mid s₀' o s₂) (rest E.fn) fun _ _ => True := by
  unfold rest
  refine RelCT.seq ((rel_wp (rel_w (l₀ := [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]) rfl [.rsp]
      (by simp) (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1 h.2) rhead_check)
    (fun _ _ h => h) (fun _ => r1_wp hp) (fun _ => r1_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2.2.2, h.2.2.2.2.2, pb.eL])
    (skip_rel fun _ _ _ => trivial) ?_
  refine RelCT.of_imp (o < L s₀) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2.2.2] at e
    have := h.1.1.1.o_le; simp at e; omega_using [e]) fun ho => ?_
  refine RelCT.seq (step [.r11, .rax] ptrs_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.2.1, h.1.2.2.1, pb.w]
      · rw [h.1.1.2.2.2.1, h.1.2.2.2.2.1])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1, h.1.1.2.2.2.1⟩, ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1,
      h.1.2.2.2.2.1⟩⟩) (fun _ => r2_wp hp) (fun _ => r2_wp hp')) ?_
  refine RelCT.seq (step [.rsi, .rdi, .rcx] copy_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.2.1, h.2.2.1, pb.src]
      · rw [h.1.2.2.1, h.2.2.2.1, pb.dst]
      · rw [h.1.2.2.2, h.2.2.2.2, pb.eL])
    (fun _ _ h => h) (fun _ => r3_wp hp ho) (fun _ => r3_wp hp' (by rw [pb.eL]; exact ho))) ?_
  refine RelCT.seq ((rel_wp (rel_w (l₀ := restArgs) (l := restArgs.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1 h.2) rargs_check)
    (fun _ _ h => h) (fun _ => r4_wp hp) (fun _ => r4_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  exact (encCall_rel hp hp' pb E (o := o) (n := L s₀ - o) (by omega_using [ho])).mono
    (fun _ _ h => ⟨h.1, by rw [← pb.eL]; exact h.2⟩) fun _ _ h => h

end

theorem encrypt_ct {M : CtxMode} (T : BlkToFn M) (E : EncFn M) :
    ConstantTime isa (Proof.AesGcm.streamEncryptToX86_64M M).pre Proof.AesGcm.streamToPub (encrypt T.fn E.fn) := by
  refine ct_of_rel (k := Proof.AesGcm.streamEncryptToX86_64M M) fun s₀ s₀' h h' hq => ?_
  have hp := SP'.ofM h
  have hp' := SP'.ofM h'
  have pb := Pub.of hq
  exact RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (head_rel hp hp' pb E)
    (RelCT.seq (RelCT.exists_ fun _ => blocks_rel hp hp' pb T) (RelCT.exists_ fun _ => rest_rel hp hp' pb E)))

end VG.Proof.AesGcm.X86_64.StreamTo
