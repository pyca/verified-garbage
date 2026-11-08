module

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.Flag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# AES-GCM decryption out of place, x86-64: what `open_to`'s frame shares

Untrusted: everything here is checked by Lean. The terms in which
`OpenToSplit/Fn.lean` states `vg_aes_gcm_open_to`'s arguments and result
(`K`, `Src`, `Dst`, …, `toPost`, `toLeak`), and the facts it uses of the
frame's pieces: a word of the stack copied (`stArg_ok`) and `dst` zeroed a
byte at a time (`zeroLoop_ok`, `bytesAt_zeros`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm dstB Fn)
open VG.Impl.AesGcm.X86_64.OpenTo (stArg wipeBody)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width)
open VG.Proof.AesGcm (arg args ret rounds)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.AesGcm (arg args ret rounds onePub openLeak)
open VG.Proof.AesGcm.X86_64.Gather (CallFn)

/-! ## `vg_aes_gcm_open(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24], tag_len = [rsp + 32])` -/

/-! ## The contract -/

section
variable (s : State)

/-- The arguments: `(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, src = [rsp + 8], len = [rsp + 16], dst = [rsp + 24],
dst_len = [rsp + 32], tag = [rsp + 40], tag_len = [rsp + 48])`. -/
abbrev K : Addr := s.gpr .rdi
abbrev R : Nat := (s.gpr .rsi).toNat
abbrev Nn : Addr := s.gpr .rdx
abbrev NL : Nat := (s.gpr .rcx).toNat
abbrev Ad : Addr := s.gpr .r8
abbrev AL : Nat := (s.gpr .r9).toNat
abbrev Src : Addr := arg s 0
abbrev L : Nat := (arg s 1).toNat
abbrev Dst : Addr := arg s 2
abbrev Tg : Addr := arg s 4
abbrev TL : Nat := (arg s 5).toNat

/-- The regions: the nonce, the additional data, the input, the output, the
received tag, the stack arguments, and the stack below the stack pointer. -/
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev sR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tR : Region := ⟨Tg s, TL s⟩
abbrev argR : Region := args s 6
abbrev stkR : Region := below (s.gpr .rsp) 2728

/-- What `vg_aes_gcm_open` computes on the arguments. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (K s) (R s)) (ctxH s.mem (K s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-- The key context. -/
abbrev kR (M : CtxMode) (s : State) : Region := ⟨K s, M.len⟩

/-- What `vg_aes_gcm_open_to` leaves: if the tag is right, the result 1 and
the plaintext at `dst`; otherwise the result 0 and zeros at `dst`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (Dst s) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak (`Spec.Gcm.openToLeak`): whether it
succeeds. -/
def toLeak (s : State) : List Nat := if ¬rounds s then [] else [if (res s).isSome then 1 else 0]

/-! ## The layout -/

/-- Two disjoint regions, within the address space and not empty, are
apart. -/
theorem apart_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h₁ : 0 < r₁.len) (h₂ : 0 < r₂.len) :
    r₁.base.toNat + r₁.len ≤ r₂.base.toNat ∨ r₂.base.toNat + r₂.len ≤ r₁.base.toNat := by
  rcases Nat.lt_or_ge (r₁.base.toNat + r₁.len) (r₂.base.toNat + 1) with c | c
  · exact .inl (by omega)
  rcases Nat.lt_or_ge (r₂.base.toNat + r₂.len) (r₁.base.toNat + 1) with d | d
  · exact .inr (by omega)
  exfalso
  rcases Nat.le_total r₁.base.toNat r₂.base.toNat with e | e
  · refine h r₂.base ?_ ?_
    · simp only [Region.Contains]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact e)]; omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine h r₁.base ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · simp only [Region.Contains]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact e)]; omega

/-! ## The blocks -/

/-- `stArg d src`: the word at `rsp + src` stored at `rsp + d`. -/
theorem stArg_ok (a : State) {Q : Addr} (hsp : a.gpr .rsp = Q) (d src : Nat)
    (hr : InRegions (a.rd ++ a.wr) (Q + BitVec.ofNat 64 src) 8) (hw : InRegions a.wr (Q + BitVec.ofNat 64 d) 8) :
    WP isa (.block (stArg d src)) a fun e =>
      e.mem = a.mem.writeW (Q + BitVec.ofNat 64 d) (a.mem.readW (Q + BitVec.ofNat 64 src) 64) ∧
      (∀ r, r ≠ .rax → e.gpr r = a.gpr r) ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [stArg, hsp, hr, hw], ?_⟩
  exact ⟨by simp [mem_setReg], fun r h₁ => by simp [gpr_setReg, h₁], rfl, rfl⟩

/-! ## The phases -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-! ## The call -/

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-! ## After the call -/

theorem zeroStep_ok (s : State) {D : Addr} {i n : Nat} (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa wipeBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) ((s.gpr .rax).setWidth 8) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₂ := Proof.AesGcm.X86_64.ea_idx s .rdi hd hi
  have wr' : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w; exact ⟨x, List.mem_append_right _ hx, hc⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff,
      Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow,
      BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies,
      implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, wipeBody, dstB,
      imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, e₂, w, wr']
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁; simp [gpr_setReg, h₁]

/-- `n` zero bytes. -/
abbrev zeros (n : Nat) : List Byte := List.replicate n 0

theorem zeros_succ (n : Nat) : zeros (n + 1) = zeros n ++ [0] := List.replicate_succ' ..

/-- The loop of `wipe`: the `n` (at least 1) bytes at `D` zeroed, with `al`
zero. -/
theorem zeroLoop_ok (s : State) {D : Addr} {n : Nat} (hd : s.gpr .rdi = D) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 0) (hax : (s.gpr .rax).setWidth 8 = 0) (pos : 1 ≤ n) (lt : n < 2 ^ 63)
    (wr : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block wipeBody) .ne) s fun s' => s'.mem = writeBytes s.mem D (zeros n) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block wipeBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (zeros i) ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
    (n - 0) _ ⟨0, rfl, pos, h10, by simp [writeBytes_nil], fun _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr'⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr''⟩ := zeroStep_ok t (by rw [g _ (by decide), hd]) r10
    (by rw [g _ (by decide), hn]) (by rw [wr']; exact Proof.AesGcm.X86_64.in_of_covers wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (zeros i).length = i := List.length_replicate ..
  have hmem : t'.mem = writeBytes s.mem D (zeros (i + 1)) := by
    rw [mem', mem, g _ (by decide), hax, zeros_succ, writeBytes_snoc s.mem D _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', Proof.AesGcm.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ => by rw [g' r h₁, g r h₁]
  by_cases he : i + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr'', wr']⟩
  · right
    exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [r10', Proof.AesGcm.X86_64.succ_ofNat], hmem, gg, by rw [rd', rd], by rw [wr'', wr']⟩

theorem bytesAt_zeros (m : Mem) (D : Addr) {n : Nat} (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m D (zeros n)) D n = zeros n := by
  have := Proof.ChaCha20Poly1305.bytesAt_writeBytes_self m D (zeros n) (by rw [List.length_replicate]; exact hn)
  rwa [List.length_replicate] at this

end VG.Proof.AesGcm.X86_64.OpenTo
