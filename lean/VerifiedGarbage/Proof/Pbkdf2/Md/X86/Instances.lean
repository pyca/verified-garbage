import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha224
import VerifiedGarbage.Impl.Pbkdf2.Md.X86
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.TaintBatch

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block`. -/
section

/-!
# HMAC and PBKDF2-HMAC over a Merkle–Damgård hash function on x86 (32-bit): the block

What HMAC's `finalize` and PBKDF2's iteration (`Impl/Pbkdf2/Md/X86.lean`)
share: a hash value at `ebx` with a block right after it, which they pad
(`pad_ok`), compress into the hash value with any verified compression
function (`cmp_ok`, against the compression contract of the hash function's
`Md`, `cmpK`; `cmp_rel` relates two runs of the call) and write the digest
into (`digest_ok`, from the hash function's own `out`, `OutOk`); and the
copies of words (`copyW_ok`) and stores of constant words (`storeW_ok`) they
are made of.
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash cpW copyW wordOf storeW tail)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.MdStream (Md)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_movm wp_store wp_addi sub_offset)
open VG.Proof.Pbkdf2.Stream.X86 (ea_at stk After after_of stk_sub stk_sub' setWidth_add toNat_add_ofNat
  rel_agree)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)

/-! ## Words -/

/-- Word `k` of `n` words at `[x + o]`, within the 32-bit address space. -/
theorem addr_word {x : BitVec 32} {o n k : Nat} (h : x.toNat + o + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    addr x (o + 4 * k) = x.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) := by
  rw [addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Copying `n` words from `[x + o₁]` to `[y + o₂]`. -/
theorem copyW_ok {src dst : Reg} (hs : src ≠ .ecx) (hd : dst ≠ .ecx) {x y : BitVec 32} {o₁ o₂ : Nat}
    (n : Nat) : ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr src = x → s.gpr dst = y → x.toNat + o₁ + 4 * n ≤ 2 ^ 32 → y.toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (o₁ + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (o₂ + 4 * k)) 4) →
    Mem.Sep (x.setWidth 64 + BitVec.ofNat 64 o₁) (4 * n) (y.setWidth 64 + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 o₁) (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (copyW src o₁ dst o₂ n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [copyW, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega) (by omega) (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun a ha hb => hsep a (by omega) (by omega_using [hb])) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cpW, List.cons_append, List.nil_append]
    refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr x (o₁ + 4 * n)) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, g₁ _ hs, hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr y (o₂ + 4 * n)) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega)) fun s₃ u₃ => ?_
    refine k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, VG.Proof.Pbkdf2.Md.X86.addr_word fx (by omega : n < n + 1), VG.Proof.Pbkdf2.Md.X86.addr_word fy (by omega : n < n + 1), m₁]
    have := VG.Proof.Hmac.Common.copy_mem s.mem (x.setWidth 64 + BitVec.ofNat 64 o₁)
      (y.setWidth 64 + BitVec.ofNat 64 o₂) n 4 (by rw [show 4 * n + 4 = 4 * (n + 1) by omega]; exact hsep)
      (by omega)
    simp only [Nat.reduceMul] at this
    rw [this, show 4 * (n + 1) = 4 * n + 4 by omega]

/-- The bytes of a little-endian word made of four bytes. -/
theorem word_bytes (a b c d : Byte) :
    (List.range (32 / 8)).map (fun j => ((a ++ b ++ c ++ d : BitVec 32).setWidth (8 * (32 / 8))).extractLsb' (8 * j) 8) =
      [d, c, b, a] := by
  simp only [show 32 / 8 = 4 from rfl, BitVec.setWidth_eq, List.range_succ,
    List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.cons.injEq,
    and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    repeat' split
    all_goals first | omega | (rw [← BitVec.getLsbD_eq_getElem]; congr 1; omega)

/-- A word of `xs` is its four bytes. -/
theorem wordOf_bytes {xs : List Byte} {k : Nat} (hk : 4 * k + 4 ≤ xs.length) :
    (List.range (32 / 8)).map (fun j => ((wordOf xs k).setWidth (8 * (32 / 8))).extractLsb' (8 * j) 8) =
      (xs.drop (4 * k)).take 4 := by
  rw [wordOf, VG.Proof.Pbkdf2.Md.X86.word_bytes]
  apply List.ext_getElem (by simp; omega)
  intro j h₁ h₂
  simp only [List.length_cons, List.length_nil] at h₁
  simp only [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 4 * k + 3 < xs.length by omega), List.getElem?_eq_getElem (show 4 * k + 2 < xs.length by omega),
    List.getElem?_eq_getElem (show 4 * k + 1 < xs.length by omega_using [hk]), List.getElem?_eq_getElem (show 4 * k < xs.length by omega),
    Option.getD_some]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- Storing the first `4 n` bytes of `xs` at `[y + o]`, a word at a time. -/
theorem storeW_ok {dst : Reg} (hd : dst ≠ .ecx) {y : BitVec 32} {o : Nat} {xs : List Byte} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), 4 * n ≤ xs.length →
    s.gpr dst = y → y.toNat + o + 4 * n ≤ 2 ^ 32 → (∀ k < n, InRegions s.wr (addr y (o + 4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o) (xs.take (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (storeW dst o xs n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hl hy fy hout k
    rw [storeW, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (by omega) hy (by omega) (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine VG.Proof.Sha256.X86.Stream.wp_movi fun s₂ u₂ => ?_
    refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr y (o + 4 * n)) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega)) fun s₃ u₃ => ?_
    refine k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) ?_
    have ht : (xs.take (4 * n)).length = 4 * n := by simp; omega
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, VG.Proof.Pbkdf2.Md.X86.addr_word fy (by omega : n < n + 1),
      Memory.writeW_bytes _ _ (wordOf xs n) ((xs.drop (4 * n)).take 4) (VG.Proof.Pbkdf2.Md.X86.wordOf_bytes (by omega)),
      Memory.writeBytes_append' _ _ _ (by rw [ht]) (by simp; omega), show 4 * (n + 1) = 4 * n + 4 by omega,
      List.take_add]

/-! ## The compression function -/

/-- The contract of a compression function `compress(state, blocks, n, scratch)`
of `H`, with `so` bytes of scratch space: updates the hash value at `state`
with the `n` blocks at `blocks` (as `Proof.Md5.compressX86` and the others). -/
def cmpK {B N L : Nat} (H : Md B N L) (so : Nat) : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, N⟩
    let blocks : Region := ⟨(VG.X86.arg s 1).setWidth 64, B * (VG.X86.arg s 2).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 3).setWidth 64, so⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + N ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + B * (VG.X86.arg s 2).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 3).toNat + so ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem ((VG.X86.arg s 0).setWidth 64) =
      H.compressBlocks (H.stateAt s.mem ((VG.X86.arg s 0).setWidth 64)) s.mem ((VG.X86.arg s 1).setWidth 64) (VG.X86.arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    VG.X86.arg s₁ 0 = VG.X86.arg s₂ 0 ∧ VG.X86.arg s₁ 1 = VG.X86.arg s₂ 1 ∧ VG.X86.arg s₁ 2 = VG.X86.arg s₂ 2 ∧ VG.X86.arg s₁ 3 = VG.X86.arg s₂ 3

/-- A verified compression function, as the code calls it: correct and
constant time, never writing `esp`, and calling nothing that uses the
stack. -/
structure CompOk {B N L : Nat} (H : Md B N L) (so : Nat) (code : Prog isa) : Prop where
  verified : Verified X86.target code (VG.Proof.Pbkdf2.Md.X86.cmpK H so)
  nosp : NoSp code
  stack : stackUse code = 0

/-- The four words a call of the compression function pushes, last to first. -/
abbrev cmp4 : List Reg := [.ebp, .ecx, .eax, .ebx]

theorem cmp4_nesp : Reg.esp ∉ VG.Proof.Pbkdf2.Md.X86.cmp4 := by decide

/-- A part of a region that `rs` covers. -/
theorem covers_off {rs : List Region} {b : Addr} {L o n : Nat} (h : Covers [⟨b, L⟩] rs) (hl : o + n ≤ L) :
    Covers [⟨b + BitVec.ofNat 64 o, n⟩] rs := fun a k hi =>
  h a k (Covers.of_sub (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, o, rfl, hl⟩) a k hi)

theorem covers_cons {rs : List Region} {r : Region} {l : List Region} (h : Covers [r] rs) (h' : Covers l rs) :
    Covers (r :: l) rs := fun a k ⟨q, hq, hc⟩ => by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h a k ⟨_, List.mem_singleton_self _, hc⟩
  · exact h' a k ⟨q, hq, hc⟩

/-- What the frame of a call of the compression function needs of the state
before its push: the hash value at `st` in `ebx` and the block after it in
`eax`, the scratch space at `sc` in `ebp`, `ecx = 1`, the regions the callee
may write, disjoint, and from the 48 bytes below `esp`, and none wrapping
around. -/
structure CmpArgs (N B so : Nat) (s : State) (st sc : BitVec 32) : Prop where
  ebx : s.gpr .ebx = st
  eax : s.gpr .eax = st + BitVec.ofNat 32 N
  ebp : s.gpr .ebp = sc
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cst : Covers [⟨st.setWidth 64, N + B⟩] s.wr
  csc : Covers [⟨sc.setWidth 64, so⟩] s.wr
  st_sc : Region.Disjoint ⟨st.setWidth 64, N + B⟩ ⟨sc.setWidth 64, so⟩
  b_st : (stk s).Disjoint ⟨st.setWidth 64, N + B⟩
  b_sc : (stk s).Disjoint ⟨sc.setWidth 64, so⟩
  nst : st.toNat + (N + B) ≤ 2 ^ 32
  nsc : sc.toNat + so ≤ 2 ^ 32

/-- The regions the compression function is given: the block and its
arguments, the hash value and its scratch space. -/
abbrev CmpArgs.rd (N B : Nat) (st sp : BitVec 32) : List Region :=
  [⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩, below sp 16]
abbrev CmpArgs.wr (N so : Nat) (st sc : BitVec 32) : List Region := [⟨st.setWidth 64, N⟩, ⟨sc.setWidth 64, so⟩]

namespace CmpArgs
variable {N B so : Nat} {s : State} {st sc : BitVec 32} (h : VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s st sc) (hcx : s.gpr .ecx = 1)
include h

theorem fit : 4 * cmp4.length + 4 ≤ (s.gpr .esp).toNat := by
  have h_sp48 := h.sp48; simp only [List.length_cons, List.length_nil]; omega


theorem a0 : VG.X86.arg (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry 0 = st := by
  rw [callEntry_arg h.fit VG.Proof.Pbkdf2.Md.X86.cmp4_nesp (by simp)]; simpa using h.ebx
theorem a1 : VG.X86.arg (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry 1 = st + BitVec.ofNat 32 N := by
  rw [callEntry_arg h.fit VG.Proof.Pbkdf2.Md.X86.cmp4_nesp (by simp)]; simpa using h.eax
theorem a3 : VG.X86.arg (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry 3 = sc := by
  rw [callEntry_arg h.fit VG.Proof.Pbkdf2.Md.X86.cmp4_nesp (by simp)]; simpa using h.ebp

include hcx in
theorem a2 : VG.X86.arg (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry 2 = 1 := by
  rw [callEntry_arg h.fit VG.Proof.Pbkdf2.Md.X86.cmp4_nesp (by simp)]; simpa using hcx

theorem blk (hB : 0 < B) : (st + BitVec.ofNat 32 N).setWidth 64 = st.setWidth 64 + BitVec.ofNat 64 N :=
  setWidth_add (by have h_nst := h.nst; omega)

include hcx in
theorem callPre {L : Nat} (H : Md B N L) (hB : 0 < B) :
    CallPre (VG.Proof.Pbkdf2.Md.X86.cmpK H so) VG.Proof.Pbkdf2.Md.X86.cmp4 (CmpArgs.rd N B st (s.gpr .esp)) (CmpArgs.wr N so st sc) s := by
  have e := h.sp48
  have fit := h.fit
  have nst := h.nst
  have a2' : (VG.X86.arg (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry 2).toNat = 1 := by rw [h.a2 hcx]; rfl
  have hb : (st + BitVec.ofNat 32 N).toNat = st.toNat + N := toNat_add_ofNat (by omega)
  have sS : Region.Sub ⟨st.setWidth 64, N⟩ ⟨st.setWidth 64, N + B⟩ := Region.sub_prefix (by omega)
  have sB : Region.Sub ⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩ ⟨st.setWidth 64, N + B⟩ := by
    rw [h.blk hB]; exact VG.Proof.Sha256.X86.Stream.sub_offset (by omega) (by omega)
  have dBS : Region.Disjoint ⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩ ⟨st.setWidth 64, N⟩ := by
    rw [h.blk hB]; exact Offset.disjoint_base _ (by omega) (by omega_using [nst])
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Pbkdf2.Md.X86.cmpK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, h.a1, h.a3, a2', callEntry_argAddr0, callEntry_esp', VG.Proof.Pbkdf2.Md.X86.cmp4,
      List.length_cons, List.length_nil]
    have sA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 4)).setWidth 64, 16⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    have sR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 4 + 4)).setWidth 64, 4⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    refine ⟨trivial, trivial, h.st_sc.sub_left sS, dBS, h.st_sc.sub_left sB, (h.b_st.sub_left sA).sub_right sS,
      h.b_sc.sub_left sA, (h.b_st.sub_left sR).sub_right sS, h.b_sc.sub_left sR, by omega, by rw [hb]; omega_using [nst],
      h.nsc, ?_⟩
    rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega_using []
  · have cB : Covers [⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩] s.wr := by
      rw [h.blk hB]; exact VG.Proof.Pbkdf2.Md.X86.covers_off h.cst (by omega)
    have cS : Covers [⟨st.setWidth 64, N⟩] s.wr := by
      have := VG.Proof.Pbkdf2.Md.X86.covers_off (o := 0) (n := N) h.cst (by omega); simpa using this
    intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cB a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    · obtain ⟨q', hq', hc'⟩ := cS a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := h.csc a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · have cS : Covers [⟨st.setWidth 64, N⟩] s.wr := by
      have := VG.Proof.Pbkdf2.Md.X86.covers_off (o := 0) (n := N) h.cst (by omega); simpa using this
    intro a n hi
    obtain ⟨q', hq', hc'⟩ := VG.Proof.Pbkdf2.Md.X86.covers_cons cS h.csc a n hi
    exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

theorem entry_frame : Frame [stk s] s.mem (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry.mem :=
  (callEntry_frame h.fit VG.Proof.Pbkdf2.Md.X86.cmp4_nesp).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons, List.length_nil]; omega) h.sp48⟩

end CmpArgs

section
variable {B N L : Nat} {H : Md B N L} {so : Nat} {name : String} {code : Prog isa} (hc : VG.Proof.Pbkdf2.Md.X86.CompOk H so code)
include hc

/-- A call of the compression function on the block after the hash value at
`st`, in a frame of its arguments: it compresses the block into the hash
value, writing only the hash value, its scratch space and the stack below
`esp`. -/
theorem cmp_frame (hB : 0 < B) {s : State} {st sc : BitVec 32} (h : VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s st sc) (hcx : s.gpr .ecx = 1)
    {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st.setWidth 64, N⟩, ⟨sc.setWidth 64, so⟩] s' →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compress (H.stateAt s.mem (st.setWidth 64)) (H.blockAt s.mem (st.setWidth 64 + BitVec.ofNat 64 N)) →
      Q s') :
    WP isa (.frame (.push VG.Proof.Pbkdf2.Md.X86.cmp4) (.call name code) (.pop .eax cmp4.length)) s Q := by
  have e := h.sp48
  refine WP.callWith hc.verified.1 hc.nosp (by simp) VG.Proof.Pbkdf2.Md.X86.cmp4_nesp
    (by rw [hc.stack]; simp only [List.length_cons, List.length_nil]; omega) (h.callPre hcx H hB)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [hc.stack] at f'
  refine hQ s' (after_of e (by simp only [List.length_cons, List.length_nil]; omega) rd' wr' cs' f') ?_
  simp only [VG.Proof.Pbkdf2.Md.X86.cmpK, arg_withRegions, State.withRegions_mem, h.a0, h.a1, h.a2 hcx] at post
  have fE := h.entry_frame
  have dS : ∀ q ∈ [stk s], (⟨st.setWidth 64, N + B⟩ : Region).Disjoint q := by
    simp only [List.mem_singleton]; rintro q rfl; exact h.b_st.symm
  have e₁ : H.stateAt (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry.mem (st.setWidth 64) = H.stateAt s.mem (st.setWidth 64) :=
    H.stateAt_congr fun i hi => fE.bytes (R := ⟨st.setWidth 64, N + B⟩) dS (by
      show N + B ≤ 2 ^ 64; have h_nst := h.nst; omega) (by show i < N + B; omega)
  have e₂ : H.blockAt (pushed VG.Proof.Pbkdf2.Md.X86.cmp4 s).callEntry.mem (st.setWidth 64 + BitVec.ofNat 64 N) =
      H.blockAt s.mem (st.setWidth 64 + BitVec.ofNat 64 N) := by
    simp only [Md.blockAt]
    refine H.parse_congr fun k hk => ?_
    rw [Memory.add_ofNat]
    exact fE.bytes (R := ⟨st.setWidth 64, N + B⟩) dS (by show N + B ≤ 2 ^ 64; have h_nst := h.nst; omega)
      (by show N + k < N + B; omega)
  rw [← m₂, post, show (1 : BitVec 32).toNat = 1 from rfl, Md.compressBlocks_one, e₁, h.blk hB, e₂]

/-- The compression of the block after the hash value at `ebx`, with `eax`
at the block. -/
theorem cmp_ok (hB : 0 < B) {s : State} {st sc : BitVec 32} (h : VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s st sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st.setWidth 64, N⟩, ⟨sc.setWidth 64, so⟩] s' →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compress (H.stateAt s.mem (st.setWidth 64)) (H.blockAt s.mem (st.setWidth 64 + BitVec.ofNat 64 N)) →
      Q s') :
    WP isa (Impl.MdStream.X86.compressAt name code .ebx .ebp) s Q := by
  refine WP.seq (VG.Proof.Sha256.X86.Stream.wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have h₁ : VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s₁ st sc :=
    { ebx := by rw [u₁.other _ (by decide), h.ebx], eax := by rw [u₁.other _ (by decide), h.eax],
      ebp := by rw [u₁.other _ (by decide), h.ebp], sp48 := by rw [u₁.other _ (by decide)]; exact h.sp48,
      cst := by rw [u₁.wr]; exact h.cst, csc := by rw [u₁.wr]; exact h.csc, st_sc := h.st_sc, b_st := by rw [stk, u₁.other _ (by decide)]; exact h.b_st,
      b_sc := by rw [stk, u₁.other _ (by decide)]; exact h.b_sc, nst := h.nst, nsc := h.nsc }
  refine VG.Proof.Pbkdf2.Md.X86.cmp_frame hc hB h₁ u₁.gpr fun s' ha e => hQ s' ?_ (by rw [e, u₁.mem])
  exact ⟨ha.rd.trans u₁.rd, ha.wr.trans u₁.wr, fun r hr => (ha.cs r hr).trans (u₁.other r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)),
    by have f := ha.frame; rw [stk, u₁.other _ (by decide), u₁.mem] at f; rw [stk]; exact f⟩

omit hc in
theorem mov1_check : ∃ hc, (VG.Taint.check taint (τr []) (.block [.mov .ecx (.imm 1)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two runs of the compression of the block, from the same hash value and
scratch space, and the same `esp`, leak the same: the call by the compression
function's contract. -/
theorem cmp_rel (hB : 0 < B) {P : State → State → Prop} {sp st sc : BitVec 32}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s st sc ∧ VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s' st sc ∧ s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (Impl.MdStream.X86.compressAt name code .ebx .ebp) fun _ _ => True := by
  have wp1 : ∀ s, VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s st sc ∧ s.gpr .esp = sp → WP isa (.block [.mov .ecx (.imm 1)]) s
      fun t => (VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so t st sc ∧ t.gpr .ecx = 1) ∧ t.gpr .esp = sp := fun s ⟨a, e⟩ =>
    VG.Proof.Sha256.X86.Stream.wp_movi fun s₁ u₁ => WP.block_nil
      ⟨⟨{ ebx := by rw [u₁.other _ (by decide), a.ebx], eax := by rw [u₁.other _ (by decide), a.eax],
          ebp := by rw [u₁.other _ (by decide), a.ebp], sp48 := by rw [u₁.other _ (by decide)]; exact a.sp48,
          cst := by rw [u₁.wr]; exact a.cst, csc := by rw [u₁.wr]; exact a.csc, st_sc := a.st_sc,
          b_st := by rw [stk, u₁.other _ (by decide)]; exact a.b_st,
          b_sc := by rw [stk, u₁.other _ (by decide)]; exact a.b_sc, nst := a.nst, nsc := a.nsc }, u₁.gpr⟩,
        by rw [u₁.other _ (by decide), e]⟩
  have r1 := rel_agree (F := fun s => VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s st sc ∧ s.gpr .esp = sp)
    (F' := fun s => VG.Proof.Pbkdf2.Md.X86.CmpArgs N B so s st sc ∧ s.gpr .esp = sp) (τr []) (fun _ _ _ _ => agree_regs (by simp))
    VG.Proof.Pbkdf2.Md.X86.mov1_check (wp1) (wp1)
  refine (r1.mono (fun s s' hp => by
      obtain ⟨a, a', e, e'⟩ := h s s' hp; exact ⟨⟨a, e⟩, ⟨a', e'⟩⟩) fun _ _ h => h).seq ?_
  refine RelCT.callWith (rs := VG.Proof.Pbkdf2.Md.X86.cmp4) hc.verified.1 hc.verified.2.1 (CmpArgs.rd N B st sp)
    (CmpArgs.wr N so st sc) fun s s' ⟨⟨⟨a, x⟩, e⟩, ⟨⟨a', x'⟩, e'⟩⟩ => ?_
  have c := a.callPre x H hB
  have c' := a'.callPre x' H hB
  rw [e] at c; rw [e'] at c'
  refine ⟨c, c', e.trans e'.symm, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions, a.a0, a'.a0]
  · simp only [arg_withRegions, a.a1, a'.a1]
  · simp only [arg_withRegions, a.a2 x, a'.a2 x']
  · simp only [arg_withRegions, a.a3, a'.a3]

end

/-! ## The digest -/

/-- `out` writes the digest of the `N`-byte hash value at `ebx` to `eax`,
writing only `ecx` and `edx`. -/
def OutOk {B N L : Nat} (H : Md B N L) (out : List Instr) : Prop :=
  ∀ s : State, (s.gpr .ebx).toNat + N ≤ 2 ^ 32 → (s.gpr .eax).toNat + N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) N → InRegions s.wr ((s.gpr .eax).setWidth 64) N →
    Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, N⟩ ⟨(s.gpr .eax).setWidth 64, N⟩ →
    WP isa (.block out) s fun s' =>
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem ((s.gpr .eax).setWidth 64) (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64)))

/-! ## The block after the hash value at `ebx` -/

/-- The sizes the proofs support, checked for each hash function by `decide`:
blocks of 64 or 128 bytes, a hash value of words, a digest of words of at
most the hash value, room in the block for the digest, the `0x80` word and
the length field, a streaming state of a hash value and a block, and the
compression function's scratch space within that of the streaming
functions. -/
structure Sizes (H : Hash) : Prop where
  B : H.B = 64 ∨ H.B = 128
  N : 0 < H.N ∧ H.N ≤ 64 ∧ H.N % 4 = 0
  D : 0 < H.D ∧ H.D ≤ H.N ∧ H.D % 4 = 0
  DL : H.D + H.L + 4 ≤ H.B
  S : H.S = H.N + H.B
  so : H.so ≤ 8 * H.st.W
  W : H.st.W ≤ 64
  F : H.D ≤ H.st.F ∧ H.st.F ≤ 64

/-- A range within a region that `rs` covers. -/
theorem inReg {rs : List Region} {b : Addr} {L o n : Nat} (h : Covers [⟨b, L⟩] rs) (hl : o + n ≤ L)
    (hL : L < 2 ^ 64) : InRegions rs (b + BitVec.ofNat 64 o) n :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hl (by omega)⟩

section
variable {H : Hash} (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H)
include hz

theorem Sizes.B4 : H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> rw [h] <;> decide

theorem Sizes.tail_length : H.tailB.length = H.B - H.D := by
  have hz_DL := hz.DL
  simp only [Hash.tailB, tail, List.length_append, List.length_singleton, List.length_replicate,
    List.length_map, List.length_range]
  omega

omit hz in
/-- `eax` at the block. -/
theorem atBlk_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .eax = s.gpr .ebx + BitVec.ofNat 32 H.N → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (H.atBlk ++ rest)) s Q := by
  simp only [Hash.atBlk, List.cons_append, List.nil_append]
  exact VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂ u₂ => k s₂ (by rw [u₂.gpr, u₁.gpr])
    (fun r hr => by rw [u₂.other r hr, u₁.other r hr]) (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr])

/-- The padding after the block's first `D` bytes. -/
theorem pad_ok {s : State} {x : BitVec 32} (hx : s.gpr .ebx = x) (hf : x.toNat + (H.N + H.B) ≤ 2 ^ 32)
    (hw : Covers [⟨x.setWidth 64, H.N + H.B⟩] s.wr) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (x.setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.pad ++ rest)) s Q := by
  have hz_D := hz.D; have hz_B4 := hz.B4; have hz_tail_length := hz.tail_length; have hz_DL := hz.DL
  have h4 : 4 * ((H.B - H.D) / 4) = H.B - H.D := by omega
  refine VG.Proof.Pbkdf2.Md.X86.storeW_ok (by decide) _ rest s Q (by omega_using [hz_tail_length]) hx (by omega_using [hz_DL, hf]) (fun j hj => ?_) fun s' g rd wr m =>
    k s' g rd wr ?_
  · rw [addr_eq (by omega_using [hj, hf])]; exact VG.Proof.Pbkdf2.Md.X86.inReg hw (by omega_using [hj]) (by omega_using [hf])
  · rw [m, h4, List.take_of_length_le (by omega)]

end

/-- The digest of the hash value into the block, from `OutOk`, the padding
after its first `D` bytes as it was. -/
theorem digest_ok {H : Hash} (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H) {md : Md H.B H.N H.L} (hout : VG.Proof.Pbkdf2.Md.X86.OutOk md H.out) {s : State}
    {x : BitVec 32} (hx : s.gpr .ebx = x) (hf : x.toNat + (H.N + H.B) ≤ 2 ^ 32)
    (hw : Covers [⟨x.setWidth 64, H.N + H.B⟩] s.wr)
    (hpad : bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s'.mem →
      bytesAt s'.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) H.D = (md.digest (md.stateAt s.mem (x.setWidth 64))).take H.D →
      bytesAt s'.mem (x.setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.digest ++ rest)) s Q := by
  have hz_D := hz.D; have hz_B4 := hz.B4; have hz_tail_length := hz.tail_length; have hz_N := hz.N; have hz_DL := hz.DL
  have h4 : 4 * ((H.N - H.D) / 4) = H.N - H.D := by omega_using [hz_N, hz_D]
  let X := x.setWidth 64
  have aN : (x + BitVec.ofNat 32 H.N).setWidth 64 = X + BitVec.ofNat 64 H.N := setWidth_add (by omega_using [hz_B4, hf])
  have tN : (x + BitVec.ofNat 32 H.N).toNat = x.toNat + H.N := toNat_add_ofNat (by omega)
  unfold Hash.digest
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86.atBlk_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  have bx₁ : s₁.gpr .ebx = x := by rw [g₁ _ (by decide), hx]
  refine WP.mono (hout s₁ (by rw [bx₁]; omega_using [hf]) (by rw [e₁, hx, tN]; omega) ?_ ?_ ?_) fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
  · rw [bx₁, rd₁, wr₁]
    have := VG.Proof.Pbkdf2.Md.X86.inReg (o := 0) (n := H.N) hw (by omega_using []) (by omega_using [hf])
    rw [BitVec.add_zero] at this
    exact Proof.Hmac.Generic.Common.InRegions.right' this
  · rw [e₁, hx, aN, wr₁]; exact VG.Proof.Pbkdf2.Md.X86.inReg hw (by omega) (by omega)
  · rw [bx₁, e₁, hx, aN]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hf])
  rw [e₁, hx, aN, bx₁, m₁] at m₂
  have hdl := md.digest_length (md.stateAt s.mem X)
  have bx₂ : s₂.gpr .ebx = x := by rw [g₂ _ (by decide) (by decide), bx₁]
  refine VG.Proof.Pbkdf2.Md.X86.storeW_ok (by decide) _ rest s₂ Q (by omega) bx₂ (by omega_using [hz_N, hz_B4, hz_D, hf]) (fun j hj => ?_)
    fun s₃ g₃ rd₃ wr₃ m₃ => k s₃ (fun r h1 h2 h3 => by rw [g₃ r h2, g₂ r h2 h3, g₁ r h1]) (by rw [rd₃, rd₂, rd₁])
      (by rw [wr₃, wr₂, wr₁]) ?_ ?_ ?_
  · rw [addr_eq (by omega), wr₂, wr₁]; exact VG.Proof.Pbkdf2.Md.X86.inReg hw (by omega) (by omega_using [hf])
  · rw [m₃, m₂, h4]
    refine (VG.WriteBytes.writeBytes_frame _ _ _ ?_).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
    · rw [hdl]; have := Offset.contains_base (X + BitVec.ofNat 64 H.N) (d := 0) (n := H.N) (k := H.B) (by omega)
        (by omega); rwa [BitVec.add_zero] at this
    · rw [List.length_take, Nat.min_eq_left (by omega_using [hz_N, hz_tail_length, hz_B4]), ← Memory.add_ofNat]
      exact Offset.contains_base _ (by omega) (by omega)
  · rw [m₃, h4, bytesAt_writeBytes_sep _ _ ?_ (by omega), m₂,
      Proof.Hmac.Generic.Common.bytesAt_take _ _ hz.D.2.1,
      Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' hdl (by omega)]
    rw [List.length_take, Nat.min_eq_left (by omega), ← Memory.add_ofNat]
    have := Offset.sep (X + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (e := H.D) (k := H.N - H.D) (.inl (by omega))
      (by omega) (by omega_using [hz_D, hf])
    rwa [BitVec.add_zero] at this
  · -- The padding: its first `N - D` bytes written back, the rest as it was.
    have hsplit : ∀ m : Mem, bytesAt m (X + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) =
        bytesAt m (X + BitVec.ofNat 64 (H.N + H.D)) (H.N - H.D) ++
          bytesAt m (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) := by
      intro m
      rw [show H.B - H.D = (H.N - H.D) + (H.B - H.N) by omega, bytesAt_add, Memory.add_ofNat,
        show H.N + H.D + (H.N - H.D) = H.N + H.N by omega_using [hz_D]]
    have hY : bytesAt s.mem (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) = H.tailB.drop (H.N - H.D) := by
      rw [← hpad, hsplit, List.drop_left' (bytesAt_length _ _ _)]
    have r₂ : bytesAt s₂.mem (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) =
        bytesAt s.mem (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) := by
      rw [m₂, ← Memory.add_ofNat]
      refine bytesAt_writeBytes_sep _ _ ?_ (by omega_using [hf])
      rw [hdl]
      have := Offset.sep (X + BitVec.ofNat 64 H.N) (d := H.N) (n := H.B - H.N) (e := 0) (k := H.N) (.inr (by omega))
        (by omega_using [hf]) (by omega_using [hf])
      rwa [BitVec.add_zero] at this
    have htl : (H.tailB.take (H.N - H.D)).length = H.N - H.D := by rw [List.length_take]; omega_using [hz_N, hz_tail_length, hz_B4]
    rw [hsplit, m₃, h4, Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' htl (by omega_using [hf]),
      bytesAt_writeBytes_sep _ _ ?_ (by omega), r₂, hY, List.take_append_drop]
    rw [htl, ← Memory.add_ofNat, ← Memory.add_ofNat]
    exact Offset.sep _ (.inr (by omega_using [hz_D])) (by omega) (by omega)

/-! ## What the proofs know of a hash function -/

/-- A hash function's x86 functions, verified: its streaming functions, as
HMAC's `init` and `finalize` call them (`HashOK`), and its `Md`, from the
initial hash value `iv`, which is the hash function of the specification
(`link`, and `back`: a state represents a message as the specification has
it if it does as `md` has it), whose stored hash value depends only on its
bytes (`reloc`), whose
padding of a `B + D`-byte message is the code's (`tail`), whose digest the
code's `out` writes, and whose compression function is verified (`comp`). -/
structure MdOk (H : Hash) where
  hH : VG.Proof.Pbkdf2.Stream.X86.HashOK H.st
  md : Md H.B H.N H.L
  iv : md.HV
  link : md.Link hH.SH iv H.D
  back : ∀ m p x, md.Repr iv m p x → hH.SH.Repr m p x
  reloc : md.Reloc
  tail : md.tailPad H.D = H.tailB
  out : VG.Proof.Pbkdf2.Md.X86.OutOk md H.out
  comp : VG.Proof.Pbkdf2.Md.X86.CompOk md H.so H.compC
  sizes : VG.Proof.Pbkdf2.Md.X86.Sizes H

end VG.Proof.Pbkdf2.Md.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes`. -/
section

/-!
# HMAC and PBKDF2-HMAC on x86 (32-bit): the Merkle–Damgård hash functions

MD5 and the SHA-512 family as `Hash`es of `Impl/Pbkdf2/Md/X86.lean`:
their streaming functions (`Proof/Pbkdf2/Stream/X86/Hashes.lean`), their
compression functions and the code writing their digests
(the `out` of their `Impl.MdStream.X86` parameters), and what the proofs know
of them (`MdOk`), from their own proofs: the `Md` of the generic streaming
proofs (`Proof/Md5/Md.lean` and the others), the digests their code writes
(from their `Shape`s), and their compression functions' contracts, which are
`cmpK`. SHA-256 and SHA-1, whose compression functions have a
variant for each backend on x86, are in `Sha256.lean` and `Sha1.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (md5H sha512H md5OK sha384OK sha512OK sha512_224OK sha512_256OK)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)

/-! ## The hash functions -/

/-- MD5: a 16-byte hash value, a little-endian length field and digest. -/
def md5M : Hash :=
  ⟨md5H, 16, 8, false, 64, "vg_md5_compress", Impl.Md5.X86.compress, Impl.Md5.X86.Stream.params.out⟩

/-- The member of the SHA-512 family with a `D`-byte digest and initial hash
value `iv`: a 64-byte hash value, a big-endian 16-byte length field, and the
digest of the whole hash value (`D` bytes of which are output). -/
def sha512M (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨sha512H D initN iv, 64, 16, true, 224, "vg_sha512_compress", Impl.Sha512.X86.compress,
    Impl.Sha512.X86.Stream.params.out⟩

def sha384M : Hash := VG.Proof.Pbkdf2.Md.X86.sha512M 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512M' : Hash := VG.Proof.Pbkdf2.Md.X86.sha512M 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224M : Hash := VG.Proof.Pbkdf2.Md.X86.sha512M 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256M : Hash := VG.Proof.Pbkdf2.Md.X86.sha512M 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

/-! ## What the proofs know of them -/

/-- The weaker register guarantee `OutOk` asks of `Impl.MdStream.X86`'s
`out`, from its `Shape`. -/
theorem outOk_of_shape {P : Impl.MdStream.X86.Params} {H : Md P.B P.N P.L} (hs : Proof.MdStream.X86.Shape H) :
    VG.Proof.Pbkdf2.Md.X86.OutOk H P.out := fun s hbx hax hin hout hd =>
  WP.mono (hs.out s hbx hax hin hout hd) fun _ ⟨g, rd, wr, m⟩ => ⟨fun r h _ => g r h, rd, wr, m⟩

def md5Ok : VG.Proof.Pbkdf2.Md.X86.MdOk VG.Proof.Pbkdf2.Md.X86.md5M where
  hH := md5OK
  md := Proof.Md5.md
  iv := Spec.Md5.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm, by decide, by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  tail := by decide
  out := VG.Proof.Pbkdf2.Md.X86.outOk_of_shape Proof.Md5.X86.Stream.shape
  comp := ⟨Proof.Md5.X86.compress_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
  sizes := ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

/-- `MdOk` for a member of the SHA-512 family, whose digest is the first `D`
bytes of the final hash value. -/
def sha512Ok {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}
    (hO : VG.Proof.Pbkdf2.Stream.X86.HashOK (sha512H D initN iv)) (hR : hO.SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, hO.SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hB : hO.SH.H.blockSize = 128)
    (hS : hO.SH.stateBytes = 192) (hD : hO.SH.digestBytes = D) (hD64 : D ≤ 64)
    (tail : Proof.Sha512.md.tailPad D = (VG.Proof.Pbkdf2.Md.X86.sha512M D initN iv).tailB) (sizes : VG.Proof.Pbkdf2.Md.X86.Sizes (VG.Proof.Pbkdf2.Md.X86.sha512M D initN iv)) :
    VG.Proof.Pbkdf2.Md.X86.MdOk (VG.Proof.Pbkdf2.Md.X86.sha512M D initN iv) where
  hH := hO
  md := Proof.Sha512.md
  iv := iv
  link := ⟨hB, hS, hD, fun _ _ _ h => by rw [hR] at h; exact h, hh, hD64, by have := sizes.DL; omega⟩
  back _ _ _ h := by rw [hR]; exact h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  tail := tail
  out := VG.Proof.Pbkdf2.Md.X86.outOk_of_shape Proof.Sha512.X86.Stream.shape
  comp := ⟨Proof.Sha512.X86.Compress.compress_verified, Proof.Sha512.X86.Stream.callee.nosp,
    Proof.Sha512.X86.Stream.callee.stack⟩
  sizes := sizes

def sha384Ok : VG.Proof.Pbkdf2.Md.X86.MdOk VG.Proof.Pbkdf2.Md.X86.sha384M := VG.Proof.Pbkdf2.Md.X86.sha512Ok sha384OK rfl (fun _ => rfl) rfl rfl rfl (by decide) (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512Ok' : VG.Proof.Pbkdf2.Md.X86.MdOk VG.Proof.Pbkdf2.Md.X86.sha512M' := VG.Proof.Pbkdf2.Md.X86.sha512Ok sha512OK rfl
  (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm)
  rfl rfl rfl (by decide) (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512_224Ok : VG.Proof.Pbkdf2.Md.X86.MdOk VG.Proof.Pbkdf2.Md.X86.sha512_224M := VG.Proof.Pbkdf2.Md.X86.sha512Ok sha512_224OK rfl (fun _ => rfl) rfl rfl rfl (by decide)
  (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512_256Ok : VG.Proof.Pbkdf2.Md.X86.MdOk VG.Proof.Pbkdf2.Md.X86.sha512_256M := VG.Proof.Pbkdf2.Md.X86.sha512Ok sha512_256OK rfl (fun _ => rfl) rfl rfl rfl (by decide)
  (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

end VG.Proof.Pbkdf2.Md.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin`. -/
section

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `finalize`, correct

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86.lean`) starts with the prologue and the
call of the hash function's streaming `finalize` on the inner state, which
writes the inner digest to `scratch` (`Proof/Pbkdf2/Stream/X86/Finalize.lean`,
whose `KR` the rest keeps). Then the inner state gets the outer hash value
and, in its buffer, the digest and the padding (`mid_ok`); one compression
(`cmpF_ok`) gives the outer hash value, whose digest is the MAC (`out_ok`):
`Md.Link.hmac_outer`.
-/

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash copyW)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK finG SavedRegs saveR savedRegs restore_ok callee_saved ea_at stk After
  setWidth_add toNat_add_ofNat)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (Pre KR E inn outer op scr inR outerR opR scR stkR T tR calR tO wr_mem
  save_sub t_sub save_t wrs kregs kregs_callee stk_eq pro_ok fin1Args_ok finCall_ok)
open VG.Proof.Hmac.Generic.Common (InRegions.right' bytesAt_writeBytes_self' bytesAt_take covers_one)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov sub_offset)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep writeBytes_at bytesAt_getD'
  xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H.st) sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ H.st.buf + H.st.F ≤ 8 * sc ∧ (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ 0 < H.D ∧ H.D ≤ H.N ∧ H.B ≤ 128 ∧ 64 ≤ H.B ∧
    H.S = H.N + H.B ∧ H.D ≤ H.st.F ∧ (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (outer s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (op s₀).toNat + H.D ≤ 2 ^ 32 := by
  have hp_ni := hp.ni; have hp_no := hp.no; have hp_np := hp.np
  have hS := hz.S
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N.1, hz.N.2.1, hz.D.1, hz.D.2.1, hz.B4.2.2, hz.B4.2.1, hS, hz.F.1,
    by rw [← hS]; exact hp.ni, by rw [← hS]; exact hp.no, hp.np⟩

/-- The compression function's scratch space. -/
abbrev cmpR (H : Hash) (s₀ : State) : Region := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀).setWidth 64, H.so⟩

theorem cmp_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpR H s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀) := by
  have := VG.Proof.Pbkdf2.Md.X86.HmacFin.bounds hz hp; exact Region.sub_prefix (by omega)

theorem save_cmp : (saveR H.st (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpR H s₀) := by
  have := VG.Proof.Pbkdf2.Md.X86.HmacFin.bounds hz hp
  exact Offset.disjoint_base _ (by omega) (by omega)

omit hp in
theorem inR_eq : VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀ = ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N + H.B⟩ := by
  rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.inR, show H.st.S = H.N + H.B from hz.S]

/-- The inner state is writable. -/
theorem cov_in {s : State} (hwr : s.wr = s₀.wr) : Covers [⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N + H.B⟩] s.wr := by
  rw [← VG.Proof.Pbkdf2.Md.X86.HmacFin.inR_eq hz, hwr]
  exact covers_one (wr_mem hp).2.1

omit hp in
/-- A part of the inner state. -/
theorem in_sub {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀) := by
  rw [VG.Proof.Pbkdf2.Md.X86.HmacFin.inR_eq hz]; exact Offset.sub_base _ h

theorem save_in {a n : Nat} (h : a + n ≤ H.N + H.B) :
    (saveR H.st (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)).Disjoint ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)).sub_right (VG.Proof.Pbkdf2.Md.X86.HmacFin.in_sub hz h)

/-- `KR` after code that writes only a part of the inner state and `eax`,
`ecx` and `edx`. -/
theorem kr_write {s s' : State} (h : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) {a n : Nat} (hl : a + n ≤ H.N + H.B)
    (hf : Frame [⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩] s.mem s'.mem) : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s' :=
  h.keep hrd hwr (fun r hr => hg r (by revert hr; decide +revert) (by revert hr; decide +revert)
    (by revert hr; decide +revert)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Md.X86.HmacFin.save_in hz hp hl)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, VG.Proof.Pbkdf2.Md.X86.HmacFin.in_sub hz hl⟩)

/-- The arguments of the compression of the inner buffer. -/
theorem cmpArgs {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s) (hax : s.gpr .eax = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ + BitVec.ofNat 32 H.N) :
    VG.Proof.Pbkdf2.Md.X86.CmpArgs H.N H.B H.so s (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) := by
  have := VG.Proof.Pbkdf2.Md.X86.HmacFin.bounds hz hp
  exact
    { ebx := hk.ebx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := VG.Proof.Pbkdf2.Md.X86.HmacFin.cov_in hz hp hk.wr
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀, (wr_mem hp).1, 0, by simp, by simp only; omega⟩
      st_sc := by rw [← VG.Proof.Pbkdf2.Md.X86.HmacFin.inR_eq hz]; exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.X86.HmacFin.cmp_sub hz hp)
      b_st := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk, ← VG.Proof.Pbkdf2.Md.X86.HmacFin.inR_eq hz]; exact hp.b_i
      b_sc := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk]; exact hp.b_s.sub_right (VG.Proof.Pbkdf2.Md.X86.HmacFin.cmp_sub hz hp)
      nst := by omega
      nsc := by omega }

end

/-! ## The outer block -/

section
variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H.st) sc s₀)
include hO hp

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it, and `eax` at the buffer. -/
theorem mid_ok {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s) (hsi : s.gpr .esi = outer s₀) :
    WP isa (.block H.finMid) s fun t => VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ t ∧ t.gpr .eax = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ + BitVec.ofNat 32 H.N ∧
      hO.md.stateAt t.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64) = hO.md.stateAt s.mem ((outer s₀).setWidth 64) ∧
      bytesAt t.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D = bytesAt s.mem (VG.Proof.Pbkdf2.Stream.X86.Finalize.T (H := H.st) s₀) H.D ∧
      bytesAt t.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB ∧
      Frame [VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀] s.mem t.mem := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := VG.Proof.Pbkdf2.Md.X86.HmacFin.bounds hz hp
  have hN4 := hz.N.2.2; have hD4 := hz.D.2.2; have tl := hz.tail_length; have hDL := hz.DL
  have hn4 : 4 * (H.N / 4) = H.N := by omega_using [hN4]
  have hd4 : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have oc : Covers [⟨(outer s₀).setWidth 64, H.N + H.B⟩] (s.rd ++ s.wr) :=
    covers_one (by rw [hk.rd, hp.rd, ← hS]; simp)
  have sc' : Covers [VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀] (s.rd ++ s.wr) := covers_one (by rw [hk.rd, hk.wr, hp.wr]; simp)
  have ic := VG.Proof.Pbkdf2.Md.X86.HmacFin.cov_in hz hp hk.wr
  simp only [Hash.finMid, List.append_assoc]
  -- The outer hash value.
  refine VG.Proof.Pbkdf2.Md.X86.copyW_ok (by decide) (by decide) (H.N / 4) _ s _ hsi hk.ebx (by omega_using [no]) (by omega_using [ni])
    (fun j hj => by rw [addr_eq (by omega_using [hj, no])]; exact VG.Proof.Pbkdf2.Md.X86.inReg oc (by omega_using [hj]) (by omega_using [hB, hN]))
    (fun j hj => by rw [addr_eq (by omega_using [hj, ni])]; exact VG.Proof.Pbkdf2.Md.X86.inReg ic (by omega) (by omega)) ?_ fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [hn4, BitVec.add_zero, BitVec.add_zero]
    have c₁ : (outerR (H := H.st) s₀).Contains ((outer s₀).setWidth 64) H.N :=
      Memory.contains_base (show H.N ≤ H.st.S by rw [show H.st.S = H.N + H.B from hz.S]; omega_using [])
    have c₂ : (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀).Contains ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64) H.N :=
      Memory.contains_base (show H.N ≤ H.st.S by rw [show H.st.S = H.N + H.B from hz.S]; omega)
    exact hp.i_o.symm.sep c₁ c₂
  rw [hn4, BitVec.add_zero, BitVec.add_zero] at m₁
  have f₁ : Frame [⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  -- The digest.
  refine VG.Proof.Pbkdf2.Md.X86.copyW_ok (by decide) (by decide) (H.D / 4) _ s₁ _ (by rw [g₁ _ (by decide), hk.ebp])
    (by rw [g₁ _ (by decide), hk.ebx]) (by omega_using [hDF, hw, hf]) (by omega_using [ni, hB64, hDN, hN])
    (fun j hj => by rw [addr_eq (by omega_using [hj, hDF, hw, hf]), rd₁, wr₁]; exact VG.Proof.Pbkdf2.Md.X86.inReg sc' (by omega_using [hj, hDF, hf]) (by omega_using [hw]))
    (fun j hj => by rw [addr_eq (by omega_using [hj, ni, hB64, hDN, hN]), wr₁]; exact VG.Proof.Pbkdf2.Md.X86.inReg ic (by omega_using [hj, hB64, hDN, hN]) (by omega)) ?_ fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  · rw [hd4]
    exact hp.i_s.symm.sep (Offset.contains_base _ (by omega_using [hDF, hf]) (by omega))
      (by rw [VG.Proof.Pbkdf2.Md.X86.HmacFin.inR_eq hz]; exact Offset.contains_base _ (by omega_using [hB64, hDN, hN]) (by omega_using [hN]))
  rw [hd4] at m₂
  have f₂ : Frame [⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  -- The padding, and `eax` at the buffer.
  refine VG.Proof.Pbkdf2.Md.X86.pad_ok hz (x := VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (by rw [g₂ _ (by decide), g₁ _ (by decide), hk.ebx]) (by omega)
    (by rw [wr₂, wr₁]; exact ic) fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  rw [← List.append_nil H.atBlk]
  refine VG.Proof.Pbkdf2.Md.X86.atBlk_ok fun s₄ e₄ g₄ m₄ rd₄ wr₄ => WP.block_nil ?_
  have f₃ : Frame [⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D), H.B - H.D⟩] s₂.mem s₄.mem := by
    rw [m₄, m₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [tl]; exact Region.contains_self _ _)
  have fI : Frame [VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀] s.mem s₄.mem :=
    ((f₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := VG.Proof.Pbkdf2.Md.X86.HmacFin.in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega_using []); rw [BitVec.add_zero] at this
        exact ⟨_, List.mem_singleton_self _, this⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, VG.Proof.Pbkdf2.Md.X86.HmacFin.in_sub hz (by omega)⟩)).trans
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, VG.Proof.Pbkdf2.Md.X86.HmacFin.in_sub hz (by omega_using [hB64, hDN, hN])⟩)
  have k₄ : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s₄ := hk.keep (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁])
    (fun r hr => by
      rw [g₄ r (by revert hr; decide +revert), g₃ r (by revert hr; decide +revert),
        g₂ r (by revert hr; decide +revert), g₁ r (by revert hr; decide +revert)]) fI
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- The bytes before the padding are not written by it, and those before the digest not by it.
  have d₃ : ∀ {a n : Nat}, a + n ≤ H.N + H.D →
      ∀ r ∈ [(⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D), H.B - H.D⟩ : Region)],
        Region.Disjoint ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl h) (by omega_using [h, hDN, hN]) (by omega_using [hB, hDN, hN])
  refine ⟨k₄, by rw [e₄, g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hk.ebx], ?_, ?_, ?_, fI⟩
  · refine hO.reloc _ _ _ _ fun i hi => ?_
    have dN : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
        ∀ r ∈ [(⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ : Region)],
          Region.Disjoint ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩ r := by
      intro a n h₁ h₂ r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ h₁ (by omega_using [h₂, hB, hN])
    rw [f₃.bytes (R := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩) (dN (by omega_using []) (by omega_using [hB64, hDN, hN])) (by show H.N ≤ 2 ^ 64; omega_using [hN]) hi,
      f₂.bytes (R := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩) (dN (by omega) (by omega_using [hB64, hDN, hN])) (by show H.N ≤ 2 ^ 64; omega) hi, m₁,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hN]), bytesAt_getD' _ _ hi]
  · rw [Memory.frame_bytesAt f₃ (d₃ (by omega)) (by omega_using [hDN, hN]), m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hDN, hN])]
    have dT : ∀ r ∈ [(⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩ : Region)], Region.Disjoint ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.T (H := H.st) s₀, H.D⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      refine (hp.i_s.symm.sub_left fun a ha => t_sub hp a (Region.sub_prefix hDF a ha)).sub_right ?_
      rw [VG.Proof.Pbkdf2.Md.X86.HmacFin.inR_eq hz]; exact Region.sub_prefix (by omega)
    exact Memory.frame_bytesAt f₁ dT (by omega)
  · rw [m₄, m₃, ← tl, bytesAt_writeBytes_self' rfl (by omega_using [tl, hB])]

/-- The compression of the inner buffer into the outer hash value. -/
theorem cmpF_ok {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s) (hax : s.gpr .eax = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s' →
      Frame [⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩, VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpR H s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64) = hO.md.compress (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64))
        (hO.md.blockAt s.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, -⟩ := VG.Proof.Pbkdf2.Md.X86.HmacFin.bounds hz hp
  have hB := hz.B4
  refine VG.Proof.Pbkdf2.Md.X86.cmp_ok hO.comp (by omega) (VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpArgs hz hp hk hax) fun s₃ ha e₃ => ?_
  have f := ha.frame
  rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk] at f
  have sI : Region.Sub ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩ (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀) := by
    have := VG.Proof.Pbkdf2.Md.X86.HmacFin.in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega_using []); rwa [BitVec.add_zero] at this
  refine k s₃ (hk.keep ha.rd ha.wr (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Stream.X86.Finalize.kregs_callee r hr)) f ?_ ?_) (f.mono (by simp)) e₃
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)).sub_right sI
    · exact VG.Proof.Pbkdf2.Md.X86.HmacFin.save_cmp hz hp
    · exact hp.b_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨_, by simp, sI⟩
    · exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.X86.HmacFin.cmp_sub hz hp⟩
    · exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀, by simp, fun _ h => h⟩

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s) :
    WP isa (.block H.finOut) s fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem ((op s₀).setWidth 64) H.D = (hO.md.digest (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64))).take H.D := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := VG.Proof.Pbkdf2.Md.X86.HmacFin.bounds hz hp
  have hD4 := hz.D.2.2
  have hd4 : 4 * (H.D / 4) = H.D := by omega
  have eD : H.st.D = H.D := rfl
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have ic := VG.Proof.Pbkdf2.Md.X86.HmacFin.cov_in hz hp hk.wr
  have hdl := hO.md.digest_length (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64))
  have sI : Region.Sub ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.N⟩ (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀) := by
    have := VG.Proof.Pbkdf2.Md.X86.HmacFin.in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega_using []); rwa [BitVec.add_zero] at this
  have hL : 8 * H.st.W + 16 ≤ 8 * sc := by omega_using [hf, hb]
  -- The epilogue, from the state the MAC is written in.
  have epi : ∀ t, VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ t → bytesAt t.mem ((op s₀).setWidth 64) H.D =
      (hO.md.digest (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64))).take H.D →
      WP isa (.block H.st.restore) t fun s' => abiPreserved s₀ s' ∧
        bytesAt s'.mem ((op s₀).setWidth 64) H.D =
          (hO.md.digest (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64))).take H.D := fun t kt ht =>
    WP.mono (VG.Proof.Pbkdf2.Stream.X86.restore_ok H.st kt.ebp kt.saved (by rw [kt.wr]; exact sR) hL hw)
      fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => by
          by_cases he : r = .esp
          · subst he; rw [ho _ (by decide) (by decide), kt.esp]
          · exact hg r (callee_saved r hr he), by rw [hm]; exact kt.ret hp⟩, by rw [hm]; exact ht⟩
  by_cases hDN' : H.D < H.N
  · simp only [Hash.finOut, hDN', ite_true, List.append_assoc]
    refine VG.Proof.Pbkdf2.Md.X86.atBlk_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ => ?_
    have k₁ : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s₁ := VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_write hz hp hk rd₁ wr₁ (fun r h1 _ _ => g₁ r h1) (a := 0) (n := 0)
      (by omega_using []) (by rw [m₁]; exact Frame.refl _ _)
    have aN : (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 = (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N :=
      setWidth_add (by omega_using [ni, hB64])
    have tN : (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ + BitVec.ofNat 32 H.N).toNat = (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).toNat + H.N := toNat_add_ofNat (by omega)
    rw [WP.block_append_iff]
    refine WP.mono (hO.out s₁ (by rw [k₁.ebx]; omega_using [ni]) (by rw [e₁, hk.ebx, tN]; omega_using [ni, hB64, hN]) ?_ ?_ ?_)
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    · rw [k₁.ebx, k₁.rd, k₁.wr]
      have := VG.Proof.Pbkdf2.Md.X86.inReg (o := 0) (n := H.N) (VG.Proof.Pbkdf2.Md.X86.HmacFin.cov_in hz hp (s := s₀) rfl) (by omega) (by omega_using [hB, hN])
      rw [BitVec.add_zero] at this
      exact InRegions.right' this
    · rw [e₁, hk.ebx, aN, k₁.wr]; exact VG.Proof.Pbkdf2.Md.X86.inReg (VG.Proof.Pbkdf2.Md.X86.HmacFin.cov_in hz hp (s := s₀) rfl) (by omega_using [hB64, hN]) (by omega_using [hB, hN])
    · rw [k₁.ebx, e₁, hk.ebx, aN]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hN])
    rw [e₁, hk.ebx, aN, k₁.ebx, m₁] at m₂
    have f₂ : Frame [⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.N⟩] s₁.mem s₂.mem := by
      rw [m₂, m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have k₂ : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s₂ := VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_write hz hp k₁ rd₂ wr₂ (fun r _ h2 h3 => g₂ r h2 h3) (by omega_using [hB64, hN]) f₂
    refine VG.Proof.Pbkdf2.Md.X86.copyW_ok (by decide) (by decide) (H.D / 4) _ s₂ _ k₂.ebx k₂.edi (by omega_using [ni, hB64, hDN, hN]) (by omega_using [np])
      (fun j hj => by
        rw [addr_eq (by omega_using [hj, ni, hB64, hDN, hN])]; exact InRegions.right' (VG.Proof.Pbkdf2.Md.X86.inReg (VG.Proof.Pbkdf2.Md.X86.HmacFin.cov_in hz hp k₂.wr) (by omega_using [hj, hB64, hDN, hN]) (by omega_using [hB, hN])))
      (fun j hj => by
        rw [addr_eq (by omega_using [hj, np]), k₂.wr]; exact ⟨_, pR, Offset.contains_base _ (by omega_using [hj, eD]) (by omega_using [hj, hDN, hN])⟩) ?_
      fun s₃ g₃ rd₃ wr₃ m₃ => ?_
    · rw [hd4, BitVec.add_zero]
      exact hp.i_p.sep (by rw [VG.Proof.Pbkdf2.Md.X86.HmacFin.inR_eq hz]; exact Offset.contains_base _ (by omega_using [hB64, hDN, hN]) (by omega_using [hN]))
        (Region.contains_self _ _)
    rw [hd4, BitVec.add_zero] at m₃
    have f₃ : Frame [opR (H := H.st) s₀] s₂.mem s₃.mem := by
      rw [m₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    have k₃ : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s₃ := k₂.keep rd₃ wr₃ (fun r hr => g₃ r (by revert hr; decide +revert)) f₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.p_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    refine epi s₃ k₃ ?_
    rw [m₃, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hDN, hN]), m₂,
      bytesAt_take _ _ (Nat.le_of_lt hDN'), bytesAt_writeBytes_self' hdl (by omega)]
  · have e : H.D = H.N := by omega_using [hDN', hDN]
    simp only [Hash.finOut, hDN', ite_false, List.cons_append]
    refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => ?_
    have k₁ : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s₁ := VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_write hz hp hk u₁.rd u₁.wr (fun r h1 _ _ => u₁.other r h1) (a := 0) (n := 0)
      (by omega) (by rw [u₁.mem]; exact Frame.refl _ _)
    rw [WP.block_append_iff]
    refine WP.mono (hO.out s₁ (by rw [k₁.ebx]; omega_using [ni]) (by rw [u₁.gpr, hk.edi]; omega_using [hDN', np]) ?_ ?_ ?_)
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    · rw [k₁.ebx, k₁.rd, k₁.wr]
      have := VG.Proof.Pbkdf2.Md.X86.inReg (o := 0) (n := H.N) (VG.Proof.Pbkdf2.Md.X86.HmacFin.cov_in hz hp (s := s₀) rfl) (by omega_using []) (by omega_using [hB, hN])
      rw [BitVec.add_zero] at this
      exact InRegions.right' this
    · rw [u₁.gpr, hk.edi, k₁.wr]; exact ⟨_, pR, Memory.contains_base (by omega_using [hDN', eD])⟩
    · rw [k₁.ebx, u₁.gpr, hk.edi]; exact hp.i_p.sub_left sI |>.sub_right (Region.sub_prefix (by omega))
    rw [u₁.gpr, hk.edi, k₁.ebx, u₁.mem] at m₂
    have f₂ : Frame [opR (H := H.st) s₀] s₁.mem s₂.mem := by
      rw [m₂, u₁.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Memory.contains_base (by omega))
    have k₂ : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s₂ := k₁.keep rd₂ wr₂
      (fun r hr => g₂ r (by revert hr; decide +revert) (by revert hr; decide +revert)) f₂
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.p_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    refine epi s₂ k₂ ?_
    rw [m₂, List.take_of_length_le (by omega_using [hDN', hdl]), bytesAt_take _ _ (Nat.le_of_eq e) (F := H.N),
      bytesAt_writeBytes_self' hdl (by omega_using [hN]), List.take_of_length_le (by omega)]

theorem correct : WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hO.hH.SH sc).post s₀ s' := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := VG.Proof.Pbkdf2.Md.X86.HmacFin.bounds hz hp
  have hl := hO.link
  have tl := hz.tail_length; have hDL := hz.DL
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Stream.X86.Finalize.pro_ok hp) fun s₁ ⟨k₁, si₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hO.hH hp k₁) fun t₁ ⟨kt₁, a₁, st₁, m₁⟩ =>
    finCall_ok hO.hH hp kt₁ a₁ fun s₂ k₂ si₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacFin.mid_ok hO hp k₂ (by rw [si₂, st₁, si₁])) fun s₃ ⟨k₃, ax₃, e₃, b₃, p₃, f₃⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpF_ok hO hp k₃ ax₃ fun s₄ k₄ f₄ e₄ => ?_)
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacFin.out_ok hO hp k₄) fun s' ⟨habi, hmac⟩ => ⟨habi, ?_⟩
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hO.hH.hB] at hk0 hcnt
  have hl0 : (xorPad k0 ipad ++ text).length = H.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until it is copied.
  have oI : ∀ r ∈ [saveR H.st (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)], Region.Disjoint (outerR (H := H.st) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)
  have o₂ : ∀ r ∈ [VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H.st) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.tR (H := H.st) s₀, calR hO.hH s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀],
      Region.Disjoint (outerR (H := H.st) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.cal_sub hO.hH hp)
    · exact hp.b_o.symm
  have rO₂ := Pbkdf2.Stream.X86.repr_keep hO.hH f₂ o₂ (m₁ ▸ Pbkdf2.Stream.X86.repr_keep hO.hH f₁ oI hrO)
  -- The inner digest.
  have dig := d₂ _ (m₁ ▸ Pbkdf2.Stream.X86.repr_keep hO.hH f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [show VG.X86.arg s₀ 3 ++ VG.X86.arg s₀ 2 = Pbkdf2.Stream.X86.countF s₀ from rfl, hcnt, hl0])
  rw [← bytesAt_take _ _ hDF] at dig
  -- The outer hash value.
  have lo : (xorPad k0 opad).length = H.B := by simp [xorPad, hk0]
  have so₂ : hO.md.stateAt s₂.mem ((outer s₀).setWidth 64) = hO.md.compressList hO.iv (xorPad k0 opad) 1 :=
    Md.stateAt_of_repr (by omega_using [hB64]) lo (hl.repr _ _ _ rO₂)
  have pad₃ : bytesAt s₃.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 H.D) (H.B - H.D) =
      hO.md.tailPad H.D := by rw [Memory.add_ofNat, p₃, hO.tail]
  rw [e₄, e₃, so₂, Md.blockAt_tailPad (by omega_using [hB64, hDN, hN]) pad₃, b₃, dig] at hmac
  show bytesAt s'.mem ((op s₀).setWidth 64) hO.hH.SH.digestBytes = hmacBlockKey hO.hH.SH.H k0 text
  rw [hO.hH.hD, hmac, hl.hmac_outer (by rw [hk0]) text]

end

end VG.Proof.Pbkdf2.Md.X86.HmacFin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFinCT`. -/
section

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `finalize`, constant time

As for HMAC's `init` (`HmacInitCT.lean`): the pieces between the calls are
checked by the taint analysis, the prologue and the arguments of the first
call, which read the arguments on the stack, with them public (`argTaint`);
the call of the streaming `finalize` is related by `fin_rel`, that of the
compression function by `cmp_rel`. Then `finalize` is verified against the
contract with the arguments read only (`finG`), and with them writable
(`finW`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (HashOK finG finW argTaint ArgsOut agree_argTaint rel_agree rel_wp stk fin_rel
  FinArgs fin5)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (Pre KR E inn outer op scr tO pre_of pro_ok fin1Args_ok finCall_ok
  stk_eq)

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 6)) (.block H.st.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6))
    (.block ([] ++ Impl.Pbkdf2.Stream.X86.Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.st.buf)) hc).isSome = true
  mid : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi, .esi]) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi]) (.block H.finOut) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 6, VG.X86.arg s₀ i = VG.X86.arg s₀' i

variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.HmacFin.Checks H)
variable {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H.st) sc s₀) (hp' : VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H.st) sc s₀') (hq : VG.Proof.Pbkdf2.Md.X86.HmacFin.PubEq s₀ s₀')

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H.st) sc t) {s : State} (hsp : s.gpr .esp = VG.Proof.Pbkdf2.Stream.X86.Finalize.E t) (hwr : s.wr = t.wr) :
    ArgsOut 6 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 6⟩ : Region) = ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.E t).setWidth 64, 4 + 24⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_i h.a_i
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_p h.a_p
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.a_s

include hq in
theorem kr_agree {s s' : State} (h : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s) (h' : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s') :
    ∀ r ∈ [Reg.esp, .ebp, .ebx, .edi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, hq.esp]
  · rw [h.ebp, h'.ebp, VG.Proof.Pbkdf2.Stream.X86.Finalize.scr, VG.Proof.Pbkdf2.Stream.X86.Finalize.scr, hq.args 5 (by decide)]
  · rw [h.ebx, h'.ebx, VG.Proof.Pbkdf2.Stream.X86.Finalize.inn, VG.Proof.Pbkdf2.Stream.X86.Finalize.inn, hq.args 0 (by decide)]
  · rw [h.edi, h'.edi, op, op, hq.args 4 (by decide)]

theorem sub_regs {l l' : List Reg} (h : ∀ r ∈ l, r ∈ l') {s s' : State} (hs : ∀ r ∈ l', s.gpr r = s'.gpr r) :
    ∀ r ∈ l, s.gpr r = s'.gpr r := fun r hr => hs r (h r hr)

include hO hc hp hp' hq

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have hH := hO.hH
  have e5 : VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀' = VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀ := (hq.args 5 (by decide)).symm
  have e0 : VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀' = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ := (hq.args 0 (by decide)).symm
  have eT : VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H.st) s₀' = VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H.st) s₀ := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.tO, VG.Proof.Pbkdf2.Stream.X86.Finalize.tO, e5]
  have e2 : VG.X86.arg s₀' 2 = VG.X86.arg s₀ 2 := (hq.args 2 (by decide)).symm
  have e3 : VG.X86.arg s₀' 3 = VG.X86.arg s₀ 3 := (hq.args 3 (by decide)).symm
  -- The prologue.
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.st.finPrologue)
      fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [] (4 + 4 * 6)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (VG.Proof.Pbkdf2.Md.X86.HmacFin.args_out hp rfl rfl) (VG.Proof.Pbkdf2.Md.X86.HmacFin.args_out hp' rfl rfl)
          hq.args) hc.pro
      (fun _ e => by subst e; exact WP.mono (VG.Proof.Pbkdf2.Stream.X86.Finalize.pro_ok hp) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ e => by subst e; exact WP.mono (VG.Proof.Pbkdf2.Stream.X86.Finalize.pro_ok hp') fun _ h => ⟨h.1, h.2.1⟩)
  -- The call of the streaming `finalize`.
  have a1 : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀'))
      (.block ([] ++ Impl.Pbkdf2.Stream.X86.Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.st.buf))
      fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧
          FinArgs hH s .ebx (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H.st) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) (VG.X86.arg s₀ 2) (VG.X86.arg s₀ 3) ∧ s.gpr .esi = outer s₀) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧
          FinArgs hH s' .ebx (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H.st) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) (VG.X86.arg s₀ 2) (VG.X86.arg s₀ 3) ∧ s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6)) (fun s s' ⟨k, _⟩ ⟨k', _⟩ =>
        agree_argTaint (VG.Proof.Pbkdf2.Md.X86.HmacFin.sub_regs (by decide) (VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_agree hq k k')) (by rw [k.esp, k'.esp, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, hq.esp])
          (VG.Proof.Pbkdf2.Md.X86.HmacFin.args_out hp k.esp k.wr) (VG.Proof.Pbkdf2.Md.X86.HmacFin.args_out hp' k'.esp k'.wr)
          fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.fin1
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp k) fun _ ⟨k₁, a, s₁, _⟩ => ⟨k₁, a, s₁.trans si⟩)
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp' k) fun _ ⟨k₁, a, s₁, _⟩ =>
        ⟨k₁, by rw [← e0, ← eT, ← e5, ← e2, ← e3]; exact a, s₁.trans si⟩)
  have c1 : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧
        FinArgs hH s .ebx (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H.st) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) (VG.X86.arg s₀ 2) (VG.X86.arg s₀ 3) ∧ s.gpr .esi = outer s₀) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧
          FinArgs hH s' .ebx (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H.st) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) (VG.X86.arg s₀ 2) (VG.X86.arg s₀ 3) ∧ s'.gpr .esi = outer s₀'))
      (.frame (.push (fin5 .ebx)) (.call H.st.finN H.st.finC) (.pop .eax (fin5 .ebx).length))
      fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_wp (fin_rel hH (sp := VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀) fun s s' ⟨⟨k, a, _⟩, ⟨k', a', _⟩⟩ =>
        ⟨a, a', k.esp, by rw [k'.esp, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, hq.esp]⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp k a fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp' k (by rw [e0, eT, e5]; exact a)
        fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
  -- The outer block.
  have mid : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀')) (.block H.finMid)
      fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ s.gpr .eax = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧ s'.gpr .eax = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (τr [.esp, .ebp, .ebx, .edi, .esi]) (fun s s' ⟨k, si⟩ ⟨k', si'⟩ => agree_regs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_agree hq k k' _ (by simp)
        · exact VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_agree hq k k' _ (by simp)
        · exact VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_agree hq k k' _ (by simp)
        · exact VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_agree hq k k' _ (by simp)
        · rw [si, si', outer, outer, hq.args 1 (by decide)]) hc.mid
      (fun _ ⟨k, si⟩ => WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacFin.mid_ok hO hp k si) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ ⟨k, si⟩ => WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacFin.mid_ok hO hp' k si) fun _ h => ⟨h.1, h.2.1⟩)
  -- The compression.
  have hB : 0 < H.B := by have := hO.sizes.B4; omega
  have cm : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ s.gpr .eax = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀ + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' ∧ s'.gpr .eax = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s' :=
    rel_wp (VG.Proof.Pbkdf2.Md.X86.cmp_rel hO.comp hB (sp := VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpArgs hO.sizes hp k a, by have := VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpArgs hO.sizes hp' k' a'; rwa [e0, e5] at this, k.esp,
          by rw [k'.esp, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, VG.Proof.Pbkdf2.Stream.X86.Finalize.E, hq.esp]⟩)
      (fun _ ⟨k, a⟩ => VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpF_ok hO hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a⟩ => VG.Proof.Pbkdf2.Md.X86.HmacFin.cmpF_ok hO hp' k a fun _ k' _ _ => k')
  -- The MAC, and the end.
  obtain ⟨_, ho⟩ := hc.out
  have out : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀ s ∧ VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H.st) sc s₀' s') (.block H.finOut)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.esp, .ebp, .ebx, .edi]) (fun _ _ h => agree_regs (VG.Proof.Pbkdf2.Md.X86.HmacFin.kr_agree hq h.1 h.2)) ho
  exact pro.seq ((a1.seq c1).seq (mid.seq (cm.seq out)))

end VG.Proof.Pbkdf2.Md.X86.HmacFin

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (finG finW)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (pre_of)

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.HmacFin.Checks H)
    (hfit : H.st.buf + H.st.F ≤ 8 * sc) (hsat : ∃ s, (finG hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacFin (finG hO.hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := VG.Proof.Pbkdf2.Md.X86.HmacFin.correct hO (VG.Proof.Pbkdf2.Stream.X86.Finalize.pre_of hO.hH sc hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (VG.Proof.Pbkdf2.Md.X86.HmacFin.ct hO hc (VG.Proof.Pbkdf2.Stream.X86.Finalize.pre_of hO.hH sc h₁ hfit) (VG.Proof.Pbkdf2.Stream.X86.Finalize.pre_of hO.hH sc h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `finalize` reads and writes, of those `finW` gives it. -/
def narrowRd (S : Nat) (s : State) : List Region := [⟨(VG.X86.arg s 1).setWidth 64, S⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (S D sc : Nat) (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, S⟩, ⟨(VG.X86.arg s 4).setWidth 64, D⟩, ⟨(VG.X86.arg s 5).setWidth 64, 8 * sc⟩]

/-- `finalize` is verified against `finW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.HmacFin.Checks H)
    (hfit : H.st.buf + H.st.F ≤ 8 * sc) (hsat : ∃ s, (finW hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacFin (finW hO.hH.SH sc) := by
  have pre : ∀ s, (finW hO.hH.SH sc).pre s → (finG hO.hH.SH sc).pre
      (s.withRegions (VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowRd hO.hH.SH.stateBytes s)
        (VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowWr hO.hH.SH.stateBytes hO.hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23⟩ := h
    simp only [finG, VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowRd, VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, h22, h23⟩
  refine Verified.narrowTo (VG.Proof.Pbkdf2.Md.X86.HmacFin.verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowRd hO.hH.SH.stateBytes) (VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowWr hO.hH.SH.stateBytes hO.hH.SH.digestBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowRd, VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Pbkdf2.Md.X86.HmacFin.narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

end VG.Proof.Pbkdf2.Md.X86.HmacFin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInit`. -/
section

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `init`, correct

HMAC's `init` (`Impl/Pbkdf2/Md/X86.lean`): the prologue (`pro_ok`), the
streaming `init` of both states (`callInit_ok`), `ipad` in every byte of the
inner state's buffer (`fill_ok`) and the key XORed into its start
(`key_ok`), the outer buffer from the inner one, word by word
(`opadW_ok`), and one compression of each buffer into its state's hash
value (`cmpI_ok`, `cmpO_ok`): each state then represents its block
(`Md.repr_block`).
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_test
  wp_movzx8 wp_store8 ofNat_beq_zero ofNat_pred ofNat_succ addr_add_ofNat)
open VG.Proof.Pbkdf2.Stream.X86 (ea_at wp_xori count_loop)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep extractLsb'_read)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)

/-! ## Words of a constant, and words XORed with a constant -/

/-- `n` words of `ecx` stored at `[y + o]`, `[y + o + 4]`, … -/
theorem fillW_ok {dst : Reg} {y : BitVec 32} {o : Nat} {b : Byte} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ecx = b ++ b ++ b ++ b →
    s.gpr dst = y → y.toNat + o + 4 * n ≤ 2 ^ 32 → (∀ k < n, InRegions s.wr (addr y (o + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o) (List.replicate (4 * n) b) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store (VG.Impl.Pbkdf2.Stream.X86.at_ dst (o + 4 * k)) .ecx) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hc hy fy hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hc hy (by omega) (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr y (o + 4 * n)) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, g₁, hy]) (by rw [wr₁]; exact hout n (by omega))
      fun s₂ u₂ => ?_
    refine k s₂ (by rw [u₂.gpr, g₁]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁]) ?_
    rw [u₂.mem, m₁, g₁, hc, VG.Proof.Pbkdf2.Md.X86.addr_word fy (by omega : n < n + 1), MdKeys.writeW_rep,
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate]) (by simp; omega), List.replicate_append_replicate,
      show 4 * n + 4 = 4 * (n + 1) by omega]

/-- The outer state's buffer, from the inner one's: `n` words of
`[ebx + N + 4 k]`, XORed with `0x6a` in every byte, into `[esi + N + 4 k]`. -/
theorem opadW_ok (H : Hash) {x y : BitVec 32} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ebx = x → s.gpr .esi = y →
    x.toNat + H.N + 4 * n ≤ 2 ^ 32 → y.toNat + H.N + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (H.N + 4 * k)) 4) →
    Region.Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ ⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ →
    (∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega) (by omega) (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      ((hsep.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega)))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr x (H.N + 4 * n)) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, g₁ _ (by decide), hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => wp_xori fun s₃ u₃ => ?_
    refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr y (H.N + 4 * n))
      (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hy])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : ((bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ (0x6a : Byte))).length =
        4 * n := by simp [bytesAt_length]
    have f₁ : Frame [⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩] s.mem s₁.mem := by
      rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
    have dX : ∀ r ∈ [(⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ : Region)],
        Region.Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n), 4⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
    rw [u₄.mem, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, VG.Proof.Pbkdf2.Md.X86.addr_word fx (by omega : n < n + 1),
      VG.Proof.Pbkdf2.Md.X86.addr_word fy (by omega : n < n + 1),
      f₁.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) dX (by decide), MdKeys.c6a, MdKeys.writeW_xorRep, m₁,
      Memory.writeBytes_append' _ _ _ (by rw [hl]) (by simp [bytesAt_length]; omega), ← List.map_append,
      ← bytesAt_add, show 4 * n + 4 = 4 * (n + 1) by omega]

/-! ## The key loop -/

/-- After `j` bytes of the key loop, from `s`: the key at `K`, its `kl`
bytes, XORed with `ipad`, written at `P`. -/
structure KeyInv (s : State) (kp p : BitVec 32) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r
  edi : t.gpr .edi = kp + BitVec.ofNat 32 j
  edx : t.gpr .edx = p + BitVec.ofNat 32 j
  ecx : t.gpr .ecx = BitVec.ofNat 32 (kl - j)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (p.setWidth 64) ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad))

theorem key_step {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (kp.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨kp.setWidth 64, kl⟩ ⟨p.setWidth 64, kl⟩) {j : Nat} (hj : j < kl) {t : State}
    (h : VG.Proof.Pbkdf2.Md.X86.KeyInv s kp p kl j t) :
    WP isa (.block [.movzx8 .eax (VG.Impl.Pbkdf2.Stream.X86.at_ .edi 0), .alu .xor .eax (.imm 0x36), .store8 (VG.Impl.Pbkdf2.Stream.X86.at_ .edx 0) .al,
      .alu .add .edi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun t' => VG.Proof.Pbkdf2.Md.X86.KeyInv s kp p kl (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hl : ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad)).length = j := by
    simp [bytesAt_length]
  have hbyte : t.mem (kp.setWidth 64 + BitVec.ofNat 64 j) = s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    refine (VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨kp.setWidth 64, kl⟩) (by
        simp only [List.mem_singleton]; rintro r rfl
        exact hsep.sub_right (Region.sub_prefix (by omega))) (by show kl ≤ 2 ^ 64; omega) hj
  refine VG.Proof.Sha256.X86.Stream.wp_movzx8 (a := kp.setWidth 64 + BitVec.ofNat 64 j)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, h.edi, VG.Proof.Sha256.X86.Stream.addr_add_ofNat (by omega_using [hj, hkp]), Nat.add_zero]) (by rw [h.rd, h.wr]; exact hin j hj)
    fun t₁ u₁ => wp_xori fun t₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store8 (a := p.setWidth 64 + BitVec.ofNat 64 j)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.edx, VG.Proof.Sha256.X86.Stream.addr_add_ofNat (by omega_using [hj, hp]), Nat.add_zero])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout j hj) fun t₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_addi fun t₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_addi fun t₅ u₅ => VG.Proof.Sha256.X86.Stream.wp_subi fun t₆ u₆ z₆ => WP.block_nil ?_
  have ecx₅ : t₅.gpr .ecx = BitVec.ofNat 32 (kl - j) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.ecx]
  have v : (t₂.gpr Reg8.al.reg).setWidth 8 = s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad := by
    show (t₂.gpr .eax).setWidth 8 = _
    rw [u₂.gpr, u₁.gpr, MdKeys.xor_byte, hbyte]; rfl
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 h3 h4 => by
      rw [u₆.other r h2, u₅.other r h3, u₄.other r h4, u₃.gpr, u₂.other r h1, u₁.other r h1, h.other r h1 h2 h3 h4],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edi, VG.Proof.Sha256.X86.Stream.ofNat_succ, BitVec.add_assoc],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edx, VG.Proof.Sha256.X86.Stream.ofNat_succ, BitVec.add_assoc],
    by rw [u₆.gpr, ecx₅, VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega_using [hj]), show kl - j - 1 = kl - (j + 1) by omega], ?_⟩, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v, u₂.mem, u₁.mem, h.mem]
    have e := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem (p.setWidth 64)
      ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad))
      (s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad) (by rw [hl]; omega_using [hj, hkp])
    rw [hl] at e
    rw [e, VG.Proof.Hmac.Generic.Common.bytesAt_snoc', List.map_append, List.map_singleton]
  · rw [z₆, ecx₅, VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega), VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- The key loop, skipped for an empty key: from the flags of `kl = 0`. -/
theorem key_ok {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (kp.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨kp.setWidth 64, kl⟩ ⟨p.setWidth 64, kl⟩)
    (h0 : VG.Proof.Pbkdf2.Md.X86.KeyInv s kp p kl 0 s) (hz : s.zf = some (decide (kl = 0))) :
    WP isa (.ite .e (.block []) Hash.keyLoop) s (VG.Proof.Pbkdf2.Md.X86.KeyInv s kp p kl kl) := by
  refine WP.ite (decide (kl = 0)) (by show VG.X86.eval .e s = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, hz])
    (fun e => WP.block_nil ?_) fun e => ?_
  · have : kl = 0 := by simpa using e
    subst this; exact h0
  · exact count_loop (by simp at e; omega) _ (fun j hj t h => VG.Proof.Pbkdf2.Md.X86.key_step hkp hp hkl hin hout hsep hj h) h0

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK initG SavedRegs saveR savedRegs save_ok restore_ok callee_saved ea_at stk
  After stk_args stk_ret arg_keep arg_contains arg_sub argAddr_eq init_frame setWidth_add toNat_add_ofNat)
open VG.Proof.Hmac.Generic.Common (off_disj off_disj0 covers_one InRegions.right' bytesAt_writeBytes_self')
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_add wp_addi wp_test sub_offset ofNat_beq_zero)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := VG.X86.arg s₀ 0
abbrev out : BitVec 32 := VG.X86.arg s₀ 1
abbrev kp : BitVec 32 := VG.X86.arg s₀ 2
abbrev kl : Nat := (VG.X86.arg s₀ 3).toNat
abbrev scr : BitVec 32 := VG.X86.arg s₀ 4
abbrev inR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64, H.N + H.B⟩
abbrev outR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64, H.N + H.B⟩
abbrev keyR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64, VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀⟩
abbrev scR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀) 4, 20⟩
abbrev retR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀) 48
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀).setWidth 64, H.so⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  kl_le : VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ ≤ H.B
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.X86.HmacInit.keyR s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀)
  i_s : (VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀)
  o_s : (VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀)
  k_i : (VG.Proof.Pbkdf2.Md.X86.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀)
  k_o : (VG.Proof.Pbkdf2.Md.X86.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀)
  k_s : (VG.Proof.Pbkdf2.Md.X86.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀)
  a_i : (VG.Proof.Pbkdf2.Md.X86.HmacInit.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀)
  a_o : (VG.Proof.Pbkdf2.Md.X86.HmacInit.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀)
  a_s : (VG.Proof.Pbkdf2.Md.X86.HmacInit.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀)
  r_i : (VG.Proof.Pbkdf2.Md.X86.HmacInit.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀)
  r_o : (VG.Proof.Pbkdf2.Md.X86.HmacInit.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀)
  r_s : (VG.Proof.Pbkdf2.Md.X86.HmacInit.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀)
  b_i : (VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀)
  b_o : (VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀)
  b_k : (VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.keyR s₀)
  b_s : (VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀)
  ni : (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  nk : (VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).toNat + VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ ≤ 2 ^ 32
  nw : (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀).toNat
  spf : (VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.st.buf ≤ 8 * sc

theorem pre_of (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {s₀ : State} (h : (initG hO.hH.SH sc).pre s₀) (hfit : H.st.buf ≤ 8 * sc) :
    VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24⟩ := h
  have hS : hO.hH.SH.stateBytes = H.N + H.B := hO.hH.hS.trans hO.sizes.S
  have hB := hO.hH.hB
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀ := by
    simp only [VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR, below]; rw [Taint.sub_setWidth h23]; rfl
  simp only [hS, hB, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, hfit⟩

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ 8 * H.st.W + 16 ≤ 8 * sc ∧ (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ H.N % 4 = 0 ∧ H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 ∧
    (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).toNat + VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ ≤ 2 ^ 32 ∧ VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ ≤ H.B := by
  have := hz.B4
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N.1, hz.N.2.1, hz.N.2.2, this.1, this.2.1, this.2.2, hp.ni, hp.no,
    hp.nk, hp.kl_le⟩

theorem save_sub : Region.Sub (saveR H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀)) (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀) := by
  have := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp; exact VG.Proof.Sha256.X86.Stream.sub_offset (by omega) (by omega)

theorem cmp_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpR (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀) := by
  have := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp; exact Region.sub_prefix (by omega)

theorem save_cmp : (saveR H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀)).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpR (H := H) s₀) := by
  have := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  exact Offset.disjoint_base _ (by omega) (by omega)

omit hz hp in
/-- A part of a state at `p`. -/
theorem st_sub (p : BitVec 32) {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨p.setWidth 64 + BitVec.ofNat 64 a, n⟩ ⟨p.setWidth 64, H.N + H.B⟩ := Offset.sub_base _ h

/-- The states, `scratch` and the stack below `esp`, as the code sees them. -/
theorem st_facts {p : BitVec 32} (hpR : p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) :
    Region.Disjoint ⟨p.setWidth 64, H.N + H.B⟩ (VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀) ∧ (VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀).Disjoint ⟨p.setWidth 64, H.N + H.B⟩ ∧
      (saveR H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀)).Disjoint ⟨p.setWidth 64, H.N + H.B⟩ ∧ p.toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
      ⟨p.setWidth 64, H.N + H.B⟩ ∈ s₀.wr := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp), hp.ni, by rw [hp.wr]; simp⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp), hp.no, by rw [hp.wr]; simp⟩

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀
  ebp : s.gpr .ebp = VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀
  esi : s.gpr .esi = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀
  saved : SavedRegs H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀) s₀ s.mem
  frame : Frame (VG.Proof.Pbkdf2.Md.X86.HmacInit.wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .esi]

theorem kregs_callee : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86.HmacInit.kregs, r ∈ calleeSaved := by decide

section
variable {sc : Nat}

theorem KR.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86.HmacInit.kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.Pbkdf2.Md.X86.HmacInit.wrs (H := H) sc s₀, Region.Sub r r') : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.esi, h.saved.frame H.st hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Md.X86.HmacInit.kregs) {v : BitVec 32}
    (u : VG.Proof.Sha256.X86.Stream.Upd s s' d v) : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

theorem stk_eq {s₀ s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) : stk s = VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀ := by rw [stk, hk.esp]

end

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀)
include hp

theorem stk_arg : (VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.argR s₀) := stk_args hp.sp48 (by have hp_spf := hp.spf; omega)

theorem stk_ret' : (VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.HmacInit.retR s₀) := stk_ret hp.sp48 (by have hp_spf := hp.spf; omega)

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.argR s₀, by rw [hp.rd]; simp, VG.Proof.Pbkdf2.Stream.X86.arg_contains rfl (by omega) (by have hp_spf := hp.spf; omega)⟩

theorem KR.argEq {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) : VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have hp_spf := hp.spf; omega) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
    · exact (VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_arg hp).symm) (by omega)

theorem KR.readArg {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, hk.esp]] at this

theorem KR.ret {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) :
    s.mem.readW ((VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀).setWidth 64) 32 = s₀.mem.readW ((VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := VG.Proof.Pbkdf2.Md.X86.HmacInit.retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_o
    · exact hp.r_s
    · exact (VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_ret' hp).symm) (by decide)

/-- The key, while `KR` holds. -/
theorem KR.key {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) :
    bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀) = bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀) :=
  Memory.frame_bytesAt hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.b_k.symm) (Nat.le_of_lt (Nat.lt_trans (VG.X86.arg s₀ 3).isLt (by decide)))

end

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H) (hp : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀)
include hz hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ fun s => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ := by
  obtain ⟨hb, hf, nw, -, hW, -⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  have sR : VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have dA : ∀ r ∈ [saveR H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀)], (VG.Proof.Pbkdf2.Md.X86.HmacInit.argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp)
  simp only [Hash.initPrologue, List.singleton_append]
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 4) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at]; rfl) (VG.Proof.Pbkdf2.Md.X86.HmacInit.argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Stream.X86.save_ok H.st (scr := VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (VG.Proof.Pbkdf2.Stream.X86.arg_sub rfl (by omega) (by have hp_spf := hp.spf; omega))) (by decide)
  have i₂ : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.Pbkdf2.Md.X86.HmacInit.argIn hp rfl rfl hi
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 0) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 1) (by
      rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl,
    by rw [u₅.gpr, u₄.mem, u₃.mem, rA 1 (by decide)],
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    (hm ▸ f₂').sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp⟩⟩,
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 0 (by decide)]⟩

end

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H) (hp : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀)
include hz hp

/-- `KR` after a call that writes `rs`, parts of our buffers. -/
theorem KR.call {s s' : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H.st (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.Pbkdf2.Md.X86.HmacInit.wrs (H := H) sc s₀, Region.Sub r r') :
    VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_eq hk] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Md.X86.HmacInit.kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hsub r hr
    · exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀, by simp, fun _ h => h⟩

/-- What a call of the streaming `init` on the state at `p`, in `st`, needs. -/
theorem initArgs {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ st = .esi ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (hsr : s.gpr st = p) :
    VG.Proof.Pbkdf2.Stream.X86.InitArgs (H := H.st) s st p := by
  have hpR : p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, dK, _, np, hin⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  exact
    { hst := hsr
      hr := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      sp48 := by rw [hk.esp]; exact hp.sp48
      cw := by rw [hk.wr, hS]; exact covers_one hin
      b_st := by rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_eq hk, hS]; exact dK
      nst := by rw [hS]; exact np }

/-- A call of the streaming `init` on the state at `p`, in `st`. -/
theorem callInit_ok (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ st = .esi ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (hsr : s.gpr st = p) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s' → s'.gpr .ebx = s.gpr .ebx →
      Frame [⟨p.setWidth 64, H.N + H.B⟩, VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀] s.mem s'.mem → hO.hH.SH.Repr s'.mem (p.setWidth 64) [] → Q s') :
    WP isa (H.st.callInit st) s Q := by
  have hpR : p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, _, dV, _, _⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  refine init_frame hO.hH (VG.Proof.Pbkdf2.Md.X86.HmacInit.initArgs hz hp hk hst hsr) fun s' ha hr => ?_
  rw [hS] at ha
  have f := ha.frame
  rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_eq hk] at f
  exact hQ s' (KR.call hz hp hk ha (by simp only [List.mem_singleton]; rintro r rfl; exact dV)
    (by
      simp only [List.mem_singleton]; rintro r rfl
      rcases hpR with rfl | rfl
      · exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀, by simp, fun _ h => h⟩)) (ha.cs .ebx (by decide)) f hr

/-- What the compression of the buffer of the state at `p`, in `ebx`, with
`eax` at the buffer, needs. -/
theorem cmpArgs {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {p : BitVec 32}
    (hpR : p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (hbx : s.gpr .ebx = p) (hax : s.gpr .eax = p + BitVec.ofNat 32 H.N) :
    VG.Proof.Pbkdf2.Md.X86.CmpArgs H.N H.B H.so s p (VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀) := by
  obtain ⟨hb, hf, nw, hso, hW, -⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  obtain ⟨dS, dK, dV, np, hin⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_facts hz hp hpR
  exact
    { ebx := hbx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := by rw [hk.wr]; exact covers_one hin
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀, by rw [hp.wr]; simp, 0, by simp, by simp only; omega⟩
      st_sc := dS.sub_right (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmp_sub hz hp)
      b_st := by rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_eq hk]; exact dK
      b_sc := by rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_eq hk]; exact hp.b_s.sub_right (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmp_sub hz hp)
      nst := np
      nsc := by omega }

/-- The compression of the buffer of the state at `p`, in `ebx`, with `eax`
at the buffer. -/
theorem cmpS_ok (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) {p : BitVec 32}
    (hpR : p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (hbx : s.gpr .ebx = p) (hax : s.gpr .eax = p + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s' → s'.gpr .ebx = p →
      Frame [⟨p.setWidth 64, H.N⟩, VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem (p.setWidth 64) = hO.md.compress (hO.md.stateAt s.mem (p.setWidth 64))
        (hO.md.blockAt s.mem (p.setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  obtain ⟨hb, hf, nw, hso, hW, hN0, hN, -, -, hB64, -⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  obtain ⟨dS, dK, dV, np, hin⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_facts hz hp hpR
  refine VG.Proof.Pbkdf2.Md.X86.cmp_ok hO.comp (by omega) (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpArgs hz hp hk hpR hbx hax) fun s' ha e => ?_
  have f := ha.frame
  rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.stk_eq hk] at f
  have sN : Region.Sub ⟨p.setWidth 64, H.N⟩ ⟨p.setWidth 64, H.N + H.B⟩ := Region.sub_prefix (by omega)
  refine hQ s' (KR.call hz hp hk ha ?_ ?_) (ha.cs .ebx (by decide) |>.trans hbx) (f.mono (by simp)) e
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV.sub_right sN
    · exact VG.Proof.Pbkdf2.Md.X86.HmacInit.save_cmp hz hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀, by simp, sN⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.outR (H := H) s₀, by simp, sN⟩
    · exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.X86.HmacInit.cmp_sub hz hp⟩

end

/-! ## The blocks -/

section
variable {sc : Nat} {s₀ : State} (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H) (hp : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀)
include hz hp

/-- A word of the buffer of the state at `p`. -/
theorem buf_word {p : BitVec 32} (hpR : p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) {k : Nat} (hk : k < H.B / 4) :
    InRegions s₀.wr (addr p (H.N + 4 * k)) 4 := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, -⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  obtain ⟨-, -, -, np, hin⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_facts hz hp hpR
  rw [addr_eq (by omega)]
  exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩

/-- `ipad` in every byte of the inner buffer, then the key's arguments. -/
theorem fill_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) :
    WP isa (.block H.fillIpad) s fun t => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ t ∧ t.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∧ t.gpr .edi = VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀ ∧
      t.gpr .edx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N ∧ t.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀) ∧
      t.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ = 0)) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) (List.replicate H.B 0x36) := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, hB64, hB, ni, -⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  simp only [Hash.fillIpad, List.cons_append]
  refine VG.Proof.Sha256.X86.Stream.wp_movi fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Md.X86.fillW_ok (H.B / 4) _ s₁ _ (b := 0x36) (u₁.gpr.trans (by decide)) (by rw [u₁.other _ (by decide), hbx])
    (by omega) (fun j hj => by rw [u₁.wr, hk.wr]; exact VG.Proof.Pbkdf2.Md.X86.HmacInit.buf_word hz hp (.inl rfl) hj) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  rw [h4] at m₂
  have f₂ : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₂.mem := by
    rw [m₂, u₁.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact Region.contains_self _ _)
  have sB : Region.Sub ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀) := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub _ (by omega)
  have k₂ : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s₂ := hk.keep (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr])
    (fun r hr => by rw [g₂, u₁.other r (by revert hr; decide +revert)]) f₂
    (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp)).sub_right sB)
    (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩)
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 2) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, k₂.esp]; rfl) (VG.Proof.Pbkdf2.Md.X86.HmacInit.argIn hp k₂.rd k₂.wr (by decide))
    fun s₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 3) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₃.other _ (by decide), k₂.esp]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact VG.Proof.Pbkdf2.Md.X86.HmacInit.argIn hp k₂.rd k₂.wr (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₅ u₅ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₆ u₆ => VG.Proof.Sha256.X86.Stream.wp_test fun s₇ f₇ z₇ => WP.block_nil ?_
  have hcx : s₇.gpr .ecx = VG.X86.arg s₀ 3 := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, k₂.readArg hp (by decide)]
  have bx₂ : s₂.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ := by rw [g₂, u₁.other _ (by decide), hbx]
  have bx : s₇.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), bx₂]
  have k₇ : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s₇ :=
    ((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).keep f₇.rd f₇.wr
      (fun r _ => by rw [f₇.gpr]) (rs := []) (by rw [f₇.mem]; exact Frame.refl _ _) (by simp) (by simp)
  refine ⟨k₇, bx, ?_, ?_, ?_, ?_, by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]⟩
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      k₂.readArg hp (by decide)]
  · rw [f₇.gpr, u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), bx₂]
  · rw [hcx, VG.Proof.Pbkdf2.Md.X86.HmacInit.kl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [z₇, ← f₇.gpr, hcx, VG.Proof.Pbkdf2.Stream.X86.test_z]


/-- The key loop: the key XORed with `ipad` over the start of the inner buffer. -/
theorem keys_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) (hdi : s.gpr .edi = VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀)
    (hdx : s.gpr .edx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N) (hcx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀))
    (hzf : s.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ = 0)))
    (hm : bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36) :
    WP isa (.ite .e (.block []) Hash.keyLoop) s fun t => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ t ∧ t.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∧
      Frame [⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem ∧
      bytesAt t.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
        (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀)).map (· ^^^ ipad) ++ List.replicate (H.B - VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀) ipad := by
  obtain ⟨-, -, -, -, -, -, hN, -, -, hB64, hB, ni, -, nk, hkl⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  have kl32 : VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  have ap : (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 = (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N :=
    setWidth_add (by omega)
  have tp : (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N).toNat = (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).toNat + H.N := toNat_add_ofNat (by omega)
  have hin : ∀ j < VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀, InRegions (s.rd ++ s.wr) ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hk.rd, hp.rd]; exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.keyR s₀, by simp, Offset.contains_base _ (by omega) (by omega_using [hj, nk])⟩
  have hout : ∀ j < VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀, InRegions s.wr ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [hk.wr, hp.wr, ap, Memory.add_ofNat]
      exact ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.inR (H := H) s₀, by simp, Offset.contains_base _ (by omega) (by omega_using [hj, nk, hN])⟩
  have hsep : Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64, VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀⟩ ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N).setWidth 64, VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀⟩ := by
    rw [ap]; exact hp.k_i.sub_right (VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub _ (by omega))
  have h0 : VG.Proof.Pbkdf2.Md.X86.KeyInv s (VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀) 0 s :=
    ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [hdi]; exact (BitVec.add_zero _).symm,
      by rw [hdx]; exact (BitVec.add_zero _).symm, by rw [hcx, Nat.sub_zero],
      by rw [show bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) 0 = [] from rfl, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86.key_ok (by omega) (by rw [tp]; omega_using [hkl, ni]) kl32 hin hout hsep h0 hzf) fun t ht => ?_
  have hl : ((bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀)).map (· ^^^ ipad)).length = VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀ := by
    simp [bytesAt_length]
  have sB := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) (a := H.N) (n := H.B) (by omega)
  have ft : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem := by
    rw [ht.mem, ap]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Memory.contains_base hkl)
  refine ⟨hk.keep ht.rd ht.wr (fun r hr => ht.other r (by revert hr; decide +revert) (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert)) ft
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩),
    by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), hbx], ft, ?_⟩
  rw [ht.mem, ap, MdKeys.bytes_over (by rw [hl]; omega) (by omega) hm, hl, hk.key hp]
  rfl


/-- The outer buffer from the inner one, and `eax` at the inner one. -/
theorem opad_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) :
    WP isa (.block H.fillOpad) s fun t => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ t ∧ t.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∧
      t.gpr .eax = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N ∧
      t.mem = VG.WriteBytes.writeBytes s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64 + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a)) := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, hB64, hB, ni, no, -⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  have sBI := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (a := H.N) (n := H.B) (by omega)
  unfold Hash.fillOpad
  refine VG.Proof.Pbkdf2.Md.X86.opadW_ok H (H.B / 4) _ s _ hbx hk.esi (by omega) (by omega)
    (fun j hj => by rw [hk.wr, hk.rd]; exact InRegions.right' (VG.Proof.Pbkdf2.Md.X86.HmacInit.buf_word hz hp (.inl rfl) hj))
    (fun j hj => by rw [hk.wr]; exact VG.Proof.Pbkdf2.Md.X86.HmacInit.buf_word hz hp (.inr rfl) hj)
    (by rw [h4]; exact (hp.i_o.sub_left sBI).sub_right sBO) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [h4] at m₁
  rw [← List.append_nil H.atBlk]
  refine VG.Proof.Pbkdf2.Md.X86.atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  have hl : ((bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₂.mem := by
    rw [m₂, m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
      (fun r hr => by rw [g₂ r (by revert hr; decide +revert), g₁ r (by revert hr; decide +revert)]) f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.o_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.save_sub hz hp)).sub_right sBO)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sBO⟩),
    by rw [g₂ _ (by decide), g₁ _ (by decide), hbx], by rw [e₂, g₁ _ (by decide), hbx], by rw [m₂, m₁]⟩


/-- The two blocks, as the constant-time proof needs them. -/
theorem blocks_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) :
    WP isa H.blocks s fun t => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ t ∧ t.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∧
      t.gpr .eax = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N := by
  have := (VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp).2.2.2.2.2.2.2.2.2.2.1
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.fill_ok hz hp hk hbx) fun s₄ ⟨k₄, b₄, d₄, x₄, c₄, z₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.keys_ok hz hp k₄ b₄ d₄ x₄ c₄ z₄ (by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega)])) fun s₅ ⟨k₅, b₅, _⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.opad_ok hz hp k₅ b₅) fun _ ⟨k₆, b₆, a₆, _⟩ => ⟨k₆, b₆, a₆⟩

omit hz hp in
/-- `ebx` at the outer state, and `eax` at its buffer. -/
theorem toOuter_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) :
    WP isa (.block H.toOuter) s fun t => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ t ∧ t.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀ ∧
      t.gpr .eax = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀ + BitVec.ofNat 32 H.N ∧ t.mem = s.mem := by
  unfold Hash.toOuter
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => ?_
  rw [← List.append_nil H.atBlk]
  refine VG.Proof.Pbkdf2.Md.X86.atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  have k₁ := hk.upd (by decide) u₁
  exact ⟨k₁.keep rd₂ wr₂ (fun r hr => g₂ r (by revert hr; decide +revert)) (rs := [])
      (by rw [m₂]; exact Frame.refl _ _) (by simp) (by simp),
    by rw [g₂ _ (by decide), u₁.gpr, hk.esi], by rw [e₂, u₁.gpr, hk.esi], by rw [m₂, u₁.mem]⟩

end


/-! ## Correctness -/

section
variable {sc : Nat} {s₀ : State} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) (hp : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀)
include hO hp

omit hp in
theorem keep_st {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) : hO.md.stateAt m' p = hO.md.stateAt m p :=
  hO.md.stateAt_congr fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd (by have := hO.sizes.N; show H.N ≤ 2 ^ 64; omega) hi

omit hp in
theorem keep_repr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N + H.B⟩ r) {x : List Byte} (hr : hO.md.Repr hO.iv m p x) :
    hO.md.Repr hO.iv m' p x :=
  hO.md.repr_congr (by have := hO.sizes.B4; omega) (fun i hi => hf.bytes (R := ⟨p, H.N + H.B⟩) hd
    (by have := hO.sizes.B4; have := hO.sizes.N; show H.N + H.B ≤ 2 ^ 64; omega) hi) hr

theorem correct :
    WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hO.hH.SH sc).post s₀ s' := by
  have hz := hO.sizes
  obtain ⟨hb, hf, nw, hso, hW, hN0, hN, hN4, hB4, hB64, hB, ni, no, nk, hkl⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.bounds hz hp
  have hl := hO.link
  -- Where things are.
  have sNI := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) (a := 0) (n := H.N) (by omega_using [])
  have sNO := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (a := 0) (n := H.N) (by omega)
  rw [BitVec.add_zero] at sNI sNO
  have sBI := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (a := H.N) (n := H.B) (by omega)
  have nb : ∀ (x : BitVec 32), Region.Disjoint ⟨x.setWidth 64, H.N⟩ ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ :=
    fun _ => Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hB, hN])
  have iv0 : ∀ {m : Mem} {p : Addr}, hO.hH.SH.Repr m p [] → hO.md.stateAt m p = hO.iv := fun h => by
    have := (hl.repr _ _ _ h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.pro_ok hz hp) fun s₁ ⟨k₁, b₁⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86.HmacInit.callInit_ok hz hp hO k₁ (.inl ⟨rfl, rfl⟩) b₁ fun s₂ k₂ b₂ _ r₂ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86.HmacInit.callInit_ok hz hp hO k₂ (.inr ⟨rfl, rfl⟩) k₂.esi fun s₃ k₃ b₃ f₃ r₃ => ?_)
  have vI₃ : hO.md.stateAt s₃.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64) = hO.iv := by
    rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left sNI
      · exact hp.b_i.symm.sub_left sNI), iv0 r₂]
  have vO₃ := iv0 r₃
  refine WP.seq (WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.fill_ok hz hp k₃ (b₃.trans (b₂.trans b₁)))
    fun s₄ ⟨k₄, b₄, d₄, x₄, c₄, z₄, m₄⟩ => ?_))
  have rep₄ : bytesAt s₄.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36 := by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega_using [hB])]
  have f₄ : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.keys_ok hz hp k₄ b₄ d₄ x₄ c₄ z₄ rep₄) fun s₅ ⟨k₅, b₅, f₅, bI₅⟩ => ?_)
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.opad_ok hz hp k₅ b₅) fun s₆ ⟨k₆, b₆, a₆, m₆⟩ => ?_
  have hl6 : ((bytesAt s₅.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f₆ : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl6]; exact Region.contains_self _ _)
  have bO₆ : bytesAt s₆.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      (bytesAt s₅.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a) := by
    rw [m₆, bytesAt_writeBytes_self' hl6 (by omega_using [hB])]
  have bI₆ : bytesAt s₆.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      bytesAt s₅.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B :=
    Memory.frame_bytesAt f₆ (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sBI).sub_right sBO) (by omega_using [hB])
  -- The hash values are those `init` left.
  have vI₆ : hO.md.stateAt s₆.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64) = hO.iv := by
    rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₆ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sNI).sub_right sBO),
      VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₄ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _), vI₃]
  have vO₆ : hO.md.stateAt s₆.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64) = hO.iv := by
    rw [VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₅ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI),
      VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₄ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI), vO₃]
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpS_ok hz hp hO k₆ (.inl rfl) b₆ a₆ fun s₇ k₇ _ f₇ e₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.toOuter_ok k₇) fun s₈ ⟨k₈, b₈, a₈, m₈⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpS_ok hz hp hO k₈ (.inr rfl) b₈ a₈ fun s₉ k₉ _ f₉ e₉ => ?_)
  -- The key.
  have hK : xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀))) ipad =
      bytesAt s₅.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B := by
    rw [bI₅, MdKeys.blockKey_short _ (by rw [bytesAt_length, hO.hH.hB]; exact hkl), MdKeys.xorPad_short,
      bytesAt_length, hO.hH.hB]
  have hKl : (xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀))) ipad).length = H.B := by
    rw [hK, bytesAt_length]
  -- The inner state.
  have rI₇ := Md.repr_block (H := hO.md) (iv := hO.iv) (by omega_using [hB64]) hKl (by rw [bI₆, hK]) (by rw [e₇, vI₆])
  have dI₉ : ∀ r ∈ [(⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64, H.N⟩ : Region), VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀],
      Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64, H.N + H.B⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.sub_right sNO
    · exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmp_sub hz hp)
    · exact hp.b_i.symm
  have rI₉ := VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_repr hO f₉ dI₉ (m₈ ▸ rI₇)
  -- The outer state.
  have d₇ : ∀ {a n : Nat}, a + n ≤ H.N + H.B → ∀ r ∈ [(⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64, H.N⟩ : Region), VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpR (H := H) s₀,
      VG.Proof.Pbkdf2.Md.X86.HmacInit.stkR s₀], Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.i_o.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub _ h)).sub_right sNI
    · exact (hp.o_s.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub _ h)).sub_right (VG.Proof.Pbkdf2.Md.X86.HmacInit.cmp_sub hz hp)
    · exact hp.b_o.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.HmacInit.st_sub _ h)
  have vO₈ : hO.md.stateAt s₈.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64) = hO.iv := by
    rw [m₈, VG.Proof.Pbkdf2.Md.X86.HmacInit.keep_st hO f₇ (by have := d₇ (a := 0) (n := H.N) (by omega_using []); rwa [BitVec.add_zero] at this), vO₆]
  have bO₈ : bytesAt s₈.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.kp s₀).setWidth 64) (VG.Proof.Pbkdf2.Md.X86.HmacInit.kl s₀))) opad := by
    rw [m₈, Memory.frame_bytesAt f₇ (d₇ (by omega)) (by omega_using [hB]), bO₆, ← hK, MdKeys.xorOpad_ipad]
  have rO₉ := Md.repr_block (H := hO.md) (iv := hO.iv) (by omega) (by rw [xorPad_length, ← xorPad_length _ ipad, hKl])
    bO₈ (by rw [e₉, vO₈])
  -- The end.
  have hsc : ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀).setWidth 64, 8 * sc⟩ ∈ s₉.wr := by rw [k₉.wr, hp.wr]; simp
  refine WP.mono (VG.Proof.Pbkdf2.Stream.X86.restore_ok H.st k₉.ebp k₉.saved hsc (by omega) nw) fun s' ⟨hm, _, _, hg, ho⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hm]; exact k₉.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₉.esp]
    · exact hg r (callee_saved r hr he)
  · show hO.hH.SH.Repr s'.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀).setWidth 64) _ ∧ hO.hH.SH.Repr s'.mem ((VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀).setWidth 64) _
    rw [hm]
    exact ⟨hO.back _ _ _ rI₉, hO.back _ _ _ rO₉⟩

end

end VG.Proof.Pbkdf2.Md.X86.HmacInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT`. -/
section

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `init`, constant time

As `finalize` (`HmacFinCT.lean`): the pieces between the calls are checked
by the taint analysis, the prologue and the blocks, which read the arguments
on the stack, with them public (`argTaint`); the calls of the streaming
`init` are related by `init_rel`, those of the compression function by
`cmp_rel`. Then `init` is verified against the contract with the arguments
read only (`initG`), and with them writable (`initW`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initG initW argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel)

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block H.initPrologue) hc).isSome = true
  blocks : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .esi] (4 + 4 * 5)) H.blocks hc).isSome = true
  toOuter : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .esi]) (.block H.toOuter) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.st.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, VG.X86.arg s₀ i = VG.X86.arg s₀' i

variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.HmacInit.Checks H)
variable {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀) (hp' : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc s₀') (hq : VG.Proof.Pbkdf2.Md.X86.HmacInit.PubEq s₀ s₀')

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : VG.Proof.Pbkdf2.Md.X86.HmacInit.Pre (H := H) sc t) {s : State} (hsp : s.gpr .esp = VG.Proof.Pbkdf2.Md.X86.HmacInit.E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(VG.Proof.Pbkdf2.Md.X86.HmacInit.E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_i h.a_i
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_o h.a_o
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.a_s

include hq in
theorem kr_agree {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s) (h' : VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s') :
    ∀ r ∈ [Reg.esp, .ebp, .esi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.esp, h'.esp, VG.Proof.Pbkdf2.Md.X86.HmacInit.E, VG.Proof.Pbkdf2.Md.X86.HmacInit.E, hq.esp]
  · rw [h.ebp, h'.ebp, VG.Proof.Pbkdf2.Md.X86.HmacInit.scr, VG.Proof.Pbkdf2.Md.X86.HmacInit.scr, hq.args 4 (by decide)]
  · rw [h.esi, h'.esi, VG.Proof.Pbkdf2.Md.X86.HmacInit.out, VG.Proof.Pbkdf2.Md.X86.HmacInit.out, hq.args 1 (by decide)]

include hO hp hp' hq

/-- A call of the streaming `init` on the state in `st` (`ebx` for `inner`,
`esi` for `outer`), with `ebx` at `inner`. -/
theorem callInit_rel {st : Reg} {p : BitVec 32} (hst : st = .ebx ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ st = .esi ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) ∧ (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀'))
      (H.st.callInit st)
      fun s s' => (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) ∧ (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀') := by
  have hz := hO.sizes
  have hst' : st = .ebx ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀' ∨ st = .esi ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, VG.Proof.Pbkdf2.Md.X86.HmacInit.inn, VG.Proof.Pbkdf2.Md.X86.HmacInit.inn, hq.args 0 (by decide)]⟩
    · exact .inr ⟨h1, by rw [h2, VG.Proof.Pbkdf2.Md.X86.HmacInit.out, VG.Proof.Pbkdf2.Md.X86.HmacInit.out, hq.args 1 (by decide)]⟩
  have hsr : ∀ {t u : State}, VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc t u → u.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn t →
      (st = .ebx ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn t ∨ st = .esi ∧ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out t) → u.gpr st = p := fun k b h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact b
    · exact k.esi
  refine rel_wp (F := fun s => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀)
    (F' := fun s => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀')
    (init_rel hO.hH (sp := VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀) (r := st) (st := p) fun s s' ⟨⟨k, b⟩, ⟨k', b'⟩⟩ =>
      ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.initArgs hz hp k hst (hsr k b hst), VG.Proof.Pbkdf2.Md.X86.HmacInit.initArgs hz hp' k' hst' (hsr k' b' hst'), k.esp,
        by rw [k'.esp, VG.Proof.Pbkdf2.Md.X86.HmacInit.E, VG.Proof.Pbkdf2.Md.X86.HmacInit.E, hq.esp]⟩)
    (fun _ ⟨k, b⟩ => VG.Proof.Pbkdf2.Md.X86.HmacInit.callInit_ok hz hp hO k hst (hsr k b hst) fun _ k' b' _ _ => ⟨k', b'.trans b⟩)
    (fun _ ⟨k, b⟩ => VG.Proof.Pbkdf2.Md.X86.HmacInit.callInit_ok hz hp' hO k hst' (hsr k b hst') fun _ k' b' _ _ => ⟨k', b'.trans b⟩)

/-- A compression of the buffer of the state at `p`, in `ebx`, with `eax`
at it. -/
theorem cmpS_rel {p p' : BitVec 32} (hpR : p = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀) (hpR' : p' = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀' ∨ p' = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀')
    (he : p' = p) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = p ∧ s.gpr .eax = p + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = p' ∧ s'.gpr .eax = p' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' := by
  have hz := hO.sizes
  have hB : 0 < H.B := by have := hz.B4; omega
  have e4 : VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀' = VG.Proof.Pbkdf2.Md.X86.HmacInit.scr s₀ := (hq.args 4 (by decide)).symm
  exact rel_wp (VG.Proof.Pbkdf2.Md.X86.cmp_rel hO.comp hB (sp := VG.Proof.Pbkdf2.Md.X86.HmacInit.E s₀) fun s s' ⟨⟨k, b, a⟩, ⟨k', b', a'⟩⟩ =>
      ⟨VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpArgs hz hp k hpR b a, by have := VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpArgs hz hp' k' hpR' b' a'; rwa [he, e4] at this, k.esp,
        by rw [k'.esp, VG.Proof.Pbkdf2.Md.X86.HmacInit.E, VG.Proof.Pbkdf2.Md.X86.HmacInit.E, hq.esp]⟩)
    (fun _ ⟨k, b, a⟩ => VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpS_ok hz hp hO k hpR b a fun _ k' _ _ _ => k')
    (fun _ ⟨k, b, a⟩ => VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpS_ok hz hp' hO k hpR' b a fun _ k' _ _ _ => k')

include hc in
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have hz := hO.sizes
  have e0 : VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀' = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ := (hq.args 0 (by decide)).symm
  have e1 : VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀' = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀ := (hq.args 1 (by decide)).symm
  -- The prologue.
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) ∧ (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀') :=
    rel_agree (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (VG.Proof.Pbkdf2.Md.X86.HmacInit.args_out hp rfl rfl) (VG.Proof.Pbkdf2.Md.X86.HmacInit.args_out hp' rfl rfl)
          hq.args) hc.pro
      (fun _ e => by subst e; exact VG.Proof.Pbkdf2.Md.X86.HmacInit.pro_ok hz hp)
      (fun _ e => by subst e; exact VG.Proof.Pbkdf2.Md.X86.HmacInit.pro_ok hz hp')
  -- The blocks.
  have blk : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀) ∧
        (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀')) H.blocks
      fun s s' => (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ ∧ s.gpr .eax = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀ + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀' ∧ s'.gpr .eax = VG.Proof.Pbkdf2.Md.X86.HmacInit.inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (argTaint [.ebp, .ebx, .esi] (4 + 4 * 5)) (fun s s' ⟨k, b⟩ ⟨k', b'⟩ =>
        agree_argTaint (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact VG.Proof.Pbkdf2.Md.X86.HmacInit.kr_agree hq k k' _ (by simp)
            · rw [b, b', e0]
            · exact VG.Proof.Pbkdf2.Md.X86.HmacInit.kr_agree hq k k' _ (by simp))
          (VG.Proof.Pbkdf2.Md.X86.HmacInit.kr_agree hq k k' _ (by simp)) (VG.Proof.Pbkdf2.Md.X86.HmacInit.args_out hp k.esp k.wr) (VG.Proof.Pbkdf2.Md.X86.HmacInit.args_out hp' k'.esp k'.wr)
          fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.blocks
      (fun _ ⟨k, b⟩ => VG.Proof.Pbkdf2.Md.X86.HmacInit.blocks_ok hz hp k b)
      (fun _ ⟨k, b⟩ => VG.Proof.Pbkdf2.Md.X86.HmacInit.blocks_ok hz hp' k b)
  -- From the inner state to the outer one.
  have tO : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s') (.block H.toOuter)
      fun s s' => (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀ ∧ s.gpr .eax = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀ + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀' ∧ s'.gpr .eax = VG.Proof.Pbkdf2.Md.X86.HmacInit.out s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (τr [.esp, .ebp, .esi]) (fun _ _ k k' => agree_regs (VG.Proof.Pbkdf2.Md.X86.HmacInit.kr_agree hq k k')) hc.toOuter
      (fun _ k => WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.toOuter_ok k) fun _ ⟨k', b, a, _⟩ => ⟨k', b, a⟩)
      (fun _ k => WP.mono (VG.Proof.Pbkdf2.Md.X86.HmacInit.toOuter_ok k) fun _ ⟨k', b, a, _⟩ => ⟨k', b, a⟩)
  -- The end.
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀ s ∧ VG.Proof.Pbkdf2.Md.X86.HmacInit.KR (H := H) sc s₀' s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Md.X86.HmacInit.kr_agree hq h.1 h.2 _ (by simp)) hr
  exact pro.seq ((VG.Proof.Pbkdf2.Md.X86.HmacInit.callInit_rel hO hp hp' hq (.inl ⟨rfl, rfl⟩)).seq
    ((VG.Proof.Pbkdf2.Md.X86.HmacInit.callInit_rel hO hp hp' hq (.inr ⟨rfl, rfl⟩)).seq
    (blk.seq ((VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpS_rel hO hp hp' hq (.inl rfl) (.inl rfl) e0).seq
    (tO.seq ((VG.Proof.Pbkdf2.Md.X86.HmacInit.cmpS_rel hO hp hp' hq (.inr rfl) (.inr rfl) e1).seq restore))))))

end VG.Proof.Pbkdf2.Md.X86.HmacInit

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initG initW)

/-- `init` is verified against `initG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.HmacInit.Checks H) (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initG hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacInit (initG hO.hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := VG.Proof.Pbkdf2.Md.X86.HmacInit.correct hO (VG.Proof.Pbkdf2.Md.X86.HmacInit.pre_of sc hO hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (VG.Proof.Pbkdf2.Md.X86.HmacInit.ct hO hc (VG.Proof.Pbkdf2.Md.X86.HmacInit.pre_of sc hO h₁ hfit) (VG.Proof.Pbkdf2.Md.X86.HmacInit.pre_of sc hO h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `init` reads and writes, of those `initW` gives it. -/
def narrowRd (s : State) : List Region :=
  [⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (S sc : Nat) (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, S⟩, ⟨(VG.X86.arg s 1).setWidth 64, S⟩, ⟨(VG.X86.arg s 4).setWidth 64, 8 * sc⟩]

/-- `init` is verified against `initW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.HmacInit.Checks H) (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (VG.Proof.Pbkdf2.Stream.X86.initW hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacInit (VG.Proof.Pbkdf2.Stream.X86.initW hO.hH.SH sc) := by
  have pre : ∀ s, (VG.Proof.Pbkdf2.Stream.X86.initW hO.hH.SH sc).pre s →
      (initG hO.hH.SH sc).pre (s.withRegions (VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowRd s)
        (VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowWr hO.hH.SH.stateBytes sc s)) := by
    intro s h
    obtain ⟨h0, _, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩ := h
    simp only [initG, VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowRd, VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowWr, arg_withRegions,
      argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
    exact ⟨h0, trivial, trivial, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩
  refine Verified.narrowTo (VG.Proof.Pbkdf2.Md.X86.HmacInit.verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowRd) (VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowWr hO.hH.SH.stateBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowRd, VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
  · obtain ⟨_, _, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Pbkdf2.Md.X86.HmacInit.narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

end VG.Proof.Pbkdf2.Md.X86.HmacInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit`. -/
section

/-!
# HMAC's `init` and `finalize` and PBKDF2's `iterate` on x86 (32-bit): the code as literals

`Hash.hmacInit`, `Hash.hmacFin` and `Hash.iterate` (`Impl/Pbkdf2/Md/X86.lean`) at each hash
function of `Hashes.lean`, as literals (`materialize_code`,
`Proof/Framework/Lit.lean`) that refer to the literals of the functions they
call (the compression functions, and the streaming `init` and `finalize`): the
registration files' `spSafe` checks evaluate them.
-/

namespace VG.Proof.Pbkdf2.Md.X86

materialize_code md5MInit := md5M.hmacInit
materialize_code md5MFinalize := md5M.hmacFin
materialize_code md5MIterate := md5M.iterate
materialize_code sha384MInit := sha384M.hmacInit
materialize_code sha384MFinalize := sha384M.hmacFin
materialize_code sha384MIterate := sha384M.iterate
materialize_code sha512MInit := sha512M'.hmacInit
materialize_code sha512MFinalize := sha512M'.hmacFin
materialize_code sha512MIterate := sha512M'.iterate
materialize_code sha512_224MInit := sha512_224M.hmacInit
materialize_code sha512_224MFinalize := sha512_224M.hmacFin
materialize_code sha512_224MIterate := sha512_224M.iterate
materialize_code sha512_256MInit := sha512_256M.hmacInit
materialize_code sha512_256MFinalize := sha512_256M.hmacFin
materialize_code sha512_256MIterate := sha512_256M.iterate

end VG.Proof.Pbkdf2.Md.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.Iterate`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86 (32-bit): correct

The iteration (`Impl/Pbkdf2/Md/X86.lean`) is correct for any hash function
whose code the proofs know (`MdOk`): `Md.hmac_step` says that its two
compressions per step compute HMAC. The arguments are on the stack: `scratch`,
`key`, `n` and `u` are loaded first (after our caller's registers are saved in
`scratch`), and `t` in each step. The loop counts the steps left in `edi` down
with `sub`, and branches on its result.
-/

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash copyW)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK iterG SavedRegs saveR savedRegs save_ok restore_ok callee_saved ea_at stk
  After setWidth_add toNat_add_ofNat stk_ret stk_args arg_contains arg_keep argAddr_eq saved_mem test_z)
open VG.Proof.Hmac.Generic.Common (InRegions.right' bytesAt_writeBytes_self' bytesAt_take covers_one)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_test
  sub_offset ofNat_beq_zero sub_ofNat eval_e eval_ne)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev key : BitVec 32 := VG.X86.arg s₀ 0
abbrev up : BitVec 32 := VG.X86.arg s₀ 1
abbrev tp : BitVec 32 := VG.X86.arg s₀ 3
abbrev scr : BitVec 32 := VG.X86.arg s₀ 4
/-- The number of steps. -/
abbrev nn : Nat := (VG.X86.arg s₀ 2).toNat
abbrev keyR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64, 2 * H.S⟩
abbrev uR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64, H.D⟩
abbrev tR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64, H.D⟩
abbrev scR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀) 4, 20⟩
abbrev retR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀) 48
/-- Byte `o` of `scratch`. -/
abbrev SA (o : Nat) : Addr := (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀).setWidth 64 + BitVec.ofNat 64 o
/-- The hash value being compressed, as `ebx` holds it, and its address;
the block is right after it. -/
abbrev hv : BitVec 32 := VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀ + BitVec.ofNat 32 H.st.buf
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀).setWidth 64, H.so⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.X86.Iterate.keyR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.uR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀]
  k_t : (VG.Proof.Pbkdf2.Md.X86.Iterate.keyR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀)
  k_s : (VG.Proof.Pbkdf2.Md.X86.Iterate.keyR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀)
  u_t : (VG.Proof.Pbkdf2.Md.X86.Iterate.uR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀)
  u_s : (VG.Proof.Pbkdf2.Md.X86.Iterate.uR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀)
  t_s : (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀)
  a_t : (VG.Proof.Pbkdf2.Md.X86.Iterate.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀)
  a_s : (VG.Proof.Pbkdf2.Md.X86.Iterate.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀)
  r_t : (VG.Proof.Pbkdf2.Md.X86.Iterate.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀)
  r_s : (VG.Proof.Pbkdf2.Md.X86.Iterate.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀)
  b_k : (VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.keyR H s₀)
  b_u : (VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.uR H s₀)
  b_t : (VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀)
  b_s : (VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀)
  nk : (VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).toNat + 2 * H.S ≤ 2 ^ 32
  nu : (VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).toNat + H.D ≤ 2 ^ 32
  nt : (VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).toNat + H.D ≤ 2 ^ 32
  nw : (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀).toNat
  spf : (VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.st.buf + H.N + H.B ≤ 8 * sc
  hz : VG.Proof.Pbkdf2.Md.X86.Sizes H

theorem pre_of {H : Hash} (hH : HashOK H.st) {sc : Nat} {s₀ : State} (h : (iterG hH.SH sc).pre s₀) (hz : VG.Proof.Pbkdf2.Md.X86.Sizes H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀ := by
    simp only [VG.Proof.Pbkdf2.Md.X86.Iterate.stkR, below]; rw [Taint.sub_setWidth h19]; rfl
  simp only [hS, hD, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hfit, hz⟩

/-! ## The parts of `scratch` -/

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀)
include hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ H.st.buf + H.N + H.B ≤ 8 * sc ∧ (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ 0 < H.D ∧ H.D ≤ H.N ∧ H.B ≤ 128 ∧ 64 ≤ H.B ∧
    H.S = H.N + H.B :=
  ⟨rfl, hp.fits, hp.nw, hp.hz.so, hp.hz.W, hp.hz.N.1, hp.hz.N.2.1, hp.hz.D.1, hp.hz.D.2.1, hp.hz.B4.2.2,
    hp.hz.B4.2.1, hp.hz.S⟩

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * sc) : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.SA s₀ o, n⟩ (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) :=
  VG.Proof.Sha256.X86.Stream.sub_offset h (by have hp_nw := hp.nw; omega)

theorem hv_eq : (VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 = VG.Proof.Pbkdf2.Md.X86.Iterate.SA s₀ H.st.buf :=
  setWidth_add (by have := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp; omega)

theorem hv_toNat : (VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).toNat = (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀).toNat + H.st.buf :=
  toNat_add_ofNat (by have := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp; omega)

/-- The hash value and the block. -/
theorem hvR_sub : Region.Sub ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N + H.B⟩ (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) := by
  rw [VG.Proof.Pbkdf2.Md.X86.Iterate.hv_eq hp]; obtain ⟨-, hf, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp; exact VG.Proof.Pbkdf2.Md.X86.Iterate.off_sub hp (by omega)

theorem cmp_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀) (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) := by
  obtain ⟨hb, hf, -, hso, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp; exact Region.sub_prefix (by omega)

theorem save_sub : Region.Sub (saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)) (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp; exact VG.Proof.Pbkdf2.Md.X86.Iterate.off_sub hp (by omega)

/-- The parts of `scratch` do not overlap. -/
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8 * sc) (hb : b + n ≤ 8 * sc) :
    Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.SA s₀ a, m⟩ ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.SA s₀ b, n⟩ :=
  VG.Proof.Hmac.Generic.Common.off_disj _ h (by have hp_nw := hp.nw; omega) (by have hp_nw := hp.nw; omega)

theorem hv_cmp : Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N + H.B⟩ (VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  rw [VG.Proof.Pbkdf2.Md.X86.Iterate.hv_eq hp]; exact Offset.disjoint_base _ (by omega) (by omega_using [hw, hf])

theorem save_hv {n : Nat} (h : n ≤ H.N + H.B) : (saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)).Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, n⟩ := by
  obtain ⟨hb, hf, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  rw [VG.Proof.Pbkdf2.Md.X86.Iterate.hv_eq hp]; exact VG.Proof.Pbkdf2.Md.X86.Iterate.part_disj hp (by omega) (by omega_using [hf, hb]) (by omega)

theorem save_cmp : (saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  exact Offset.disjoint_base _ (by omega) (by omega)

theorem stk_arg : (VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.argR s₀) := stk_args hp.sp48 (by have hp_spf := hp.spf; omega)

theorem stk_ret' : (VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.retR s₀) := stk_ret hp.sp48 (by have hp_spf := hp.spf; omega)

theorem t_hv {n : Nat} (h : n ≤ H.N + H.B) : Region.Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀) ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, n⟩ :=
  hp.t_s.sub_right fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Region.sub_prefix h a ha)

theorem t_blk : Region.Disjoint (VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀) ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ := by
  obtain ⟨hb, hf, hw, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  refine hp.t_s.sub_right fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Offset.sub_base _ (by omega) a ha)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: `T`, `scratch` and the stack below `esp`. -/
abbrev wrs (H : Hash) (sc : Nat) (s₀ : State) : List Region := [VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀]

/-- The registers and memory kept from the prologue on, with `m` steps left. -/
structure KR (H : Hash) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀
  ebp : s.gpr .ebp = VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀
  ebx : s.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀
  esi : s.gpr .esi = VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀
  edi : s.gpr .edi = BitVec.ofNat 32 m
  saved : SavedRegs H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀) s₀ s.mem
  frame : Frame (VG.Proof.Pbkdf2.Md.X86.Iterate.wrs H sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .ebx, .esi, .edi]

theorem kregs_callee : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86.Iterate.kregs, r ∈ calleeSaved := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {m : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86.Iterate.kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.Pbkdf2.Md.X86.Iterate.wrs H sc s₀, Region.Sub r r') : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.ebx, (hg _ (by simp)).trans h.esi, (hg _ (by simp)).trans h.edi,
    h.saved.frame H.st hf hs, h.frame.trans (hf.sub hsub)⟩

/-- `KR` after code that writes only `eax`, `ecx` and `edx` and a part of
`scratch` other than where our caller's registers are. -/
theorem KR.write {m : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) {R : Region} (hf : Frame [R] s.mem s'.mem)
    (hs : (saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)).Disjoint R) (hsub : ∃ r' ∈ VG.Proof.Pbkdf2.Md.X86.Iterate.wrs H sc s₀, Region.Sub R r') : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s' :=
  h.keep hrd hwr (fun r hr => hg r (by revert hr; decide +revert) (by revert hr; decide +revert)
    (by revert hr; decide +revert)) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub)

theorem stk_eq {m : Nat} {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) : stk s = VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀ := by rw [stk, hk.esp]

end

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀)
include hp

theorem mem_wr : VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem argR_in : VG.Proof.Pbkdf2.Md.X86.Iterate.argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.argR s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.argR_in hp, VG.Proof.Pbkdf2.Stream.X86.arg_contains rfl (by omega) (by have hp_spf := hp.spf; omega)⟩

theorem KR.argEq {m : Nat} {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) {i : Nat} (hi : i < 5) :
    VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have hp_spf := hp.spf; omega) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_t
    · exact hp.a_s
    · exact (VG.Proof.Pbkdf2.Md.X86.Iterate.stk_arg hp).symm) (by omega)

theorem KR.readArg {m : Nat} {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, hk.esp]] at this

theorem KR.ret {m : Nat} {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) :
    s.mem.readW ((VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀).setWidth 64) 32 = s₀.mem.readW ((VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := VG.Proof.Pbkdf2.Md.X86.Iterate.retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_t
    · exact hp.r_s
    · exact (VG.Proof.Pbkdf2.Md.X86.Iterate.stk_ret' hp).symm) (by decide)

/-- `KR` after a call that writes parts of `scratch`. -/
theorem KR.call {m : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws, (saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)).Disjoint r) (hsub : ∀ r ∈ ws, Region.Sub r (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀)) :
    VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s' := by
  have f := ha.frame
  rw [VG.Proof.Pbkdf2.Md.X86.Iterate.stk_eq h] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Md.X86.Iterate.kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.b_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86.Iterate.save_sub hp)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, hsub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀, by simp, fun _ h => h⟩

/-- The hash value and block are writable. -/
theorem cov_hv {s : State} (hwr : s.wr = s₀.wr) : Covers [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N + H.B⟩] s.wr := by
  obtain ⟨hb, hf, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  rw [VG.Proof.Pbkdf2.Md.X86.Iterate.hv_eq hp, hwr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, (VG.Proof.Pbkdf2.Md.X86.Iterate.mem_wr hp).1, H.st.buf, rfl, by simp only; omega_using [hf]⟩

/-- The arguments of the compression of the block. -/
theorem cmpArgs {m : Nat} {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) (hax : s.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ + BitVec.ofNat 32 H.N) :
    VG.Proof.Pbkdf2.Md.X86.CmpArgs H.N H.B H.so s (VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀) (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  have := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_toNat hp
  exact
    { ebx := hk.ebx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp hk.wr
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, (VG.Proof.Pbkdf2.Md.X86.Iterate.mem_wr hp).1, 0, by simp, by simp only; omega⟩
      st_sc := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_cmp hp
      b_st := by rw [VG.Proof.Pbkdf2.Md.X86.Iterate.stk_eq hk]; exact hp.b_s.sub_right (VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp)
      b_sc := by rw [VG.Proof.Pbkdf2.Md.X86.Iterate.stk_eq hk]; exact hp.b_s.sub_right (VG.Proof.Pbkdf2.Md.X86.Iterate.cmp_sub hp)
      nst := by omega
      nsc := by omega }

/-- The key's bytes are as on entry. -/
theorem key_bytes {m : Nat} {s : State} (hk : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) {i : Nat} (hi : i < 2 * H.S) :
    s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 i) :=
  hk.frame.bytes (R := VG.Proof.Pbkdf2.Md.X86.Iterate.keyR H s₀) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.k_t
    · exact hp.k_s
    · exact hp.b_k.symm) (by show 2 * H.S ≤ 2 ^ 64; have hp_nk := hp.nk; omega) hi

end

/-! ## The loop invariant -/

section
variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  hO.md.step H.D (hO.md.stateAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64))
    (hO.md.stateAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 H.S))

end

/-- The loop invariant, with `m` steps left. -/
structure Inv {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop
    extends VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s where
  pad : bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB
  le : m ≤ VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀
  val : Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.Md.X86.Iterate.stepM hO s₀) (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀) (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64) H.D)
      (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D) =
    Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.Md.X86.Iterate.stepM hO s₀) m (bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)
      (bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D)

/-! ## Loading a hash value of the key and compressing the block into it -/

section
variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀)
include hp

/-- The block, after the hash value, is outside what the load and the
compression write. -/
theorem blk_disj {a n : Nat} (h₁ : H.N ≤ a) (h₂ : a + n ≤ H.N + H.B) :
    ∀ r ∈ [(⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩ : Region), VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀],
      Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
  obtain ⟨hb, hf, hw, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  have := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_toNat hp
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ h₁ (by omega_using [hw, hf, h₂])
  · exact (VG.Proof.Pbkdf2.Md.X86.Iterate.hv_cmp hp).sub_left (Offset.sub_base _ (by omega))
  · exact (hp.b_s.sub_right fun a' ha' => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a' (Offset.sub_base _ (by omega) a' ha')).symm

/-- Loading the key's hash value at `key + o` into the hash value being
compressed, and `eax` at the block. -/
theorem load_ok {o : Nat} (ho : o + H.N ≤ 2 * H.S) {m : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s' → s'.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ + BitVec.ofNat 32 H.N →
      Frame [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩] s.mem s'.mem →
      hO.md.stateAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64) = hO.md.stateAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.loadKey o ++ H.atBlk ++ rest)) s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  have hN4 := hp.hz.N.2.2
  have hn4 : 4 * (H.N / 4) = H.N := by omega_using [hN4]
  have hvt := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_toNat hp
  have nk := hp.nk
  have kc : Covers [VG.Proof.Pbkdf2.Md.X86.Iterate.keyR H s₀] (s.rd ++ s.wr) := covers_one (by rw [h.rd, hp.rd]; simp)
  rw [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86.copyW_ok (by decide) (by decide) (H.N / 4) _ s _ h.esi h.ebx (by omega_using [nk, ho]) (by omega_using [hvt, hw, hf])
    (fun j hj => by rw [addr_eq (by omega_using [hj, nk, ho])]; exact VG.Proof.Pbkdf2.Md.X86.inReg kc (by omega_using [hj, ho]) (by omega_using [hS, hw, hf]))
    (fun j hj => by rw [addr_eq (by omega_using [hj, hvt, hw, hf])]; exact VG.Proof.Pbkdf2.Md.X86.inReg (VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp h.wr) (by omega_using [hj]) (by omega_using [hw, hf])) ?_
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [hn4]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
      (by rw [BitVec.add_zero, VG.Proof.Pbkdf2.Md.X86.Iterate.hv_eq hp]; exact Offset.contains_base _ (by omega_using [hf]) (by omega))
  rw [hn4, BitVec.add_zero] at m₁
  have f₁ : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine VG.Proof.Pbkdf2.Md.X86.atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => ?_
  have k₂ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s₂ := h.write (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    (fun r h1 h2 _ => by rw [g₂ r h1, g₁ r h2]) (m₂ ▸ f₁) (VG.Proof.Pbkdf2.Md.X86.Iterate.save_hv hp (by omega))
    ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Region.sub_prefix (by omega) a ha)⟩
  refine k s₂ k₂ (by rw [e₂, g₁ _ (by decide), h.ebx]) (m₂ ▸ f₁) ?_
  refine hO.reloc _ _ _ _ fun i hi => ?_
  rw [m₂, m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi, Memory.add_ofNat]
  exact VG.Proof.Pbkdf2.Md.X86.Iterate.key_bytes hp h (by omega_using [hi, ho])

/-- The compression of the block into the hash value. -/
theorem cmpS_ok {m : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s) (hax : s.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s' → Frame [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩, VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64) = hO.md.compress (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64))
        (hO.md.blockAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  refine VG.Proof.Pbkdf2.Md.X86.cmp_ok hO.comp (by omega) (VG.Proof.Pbkdf2.Md.X86.Iterate.cmpArgs hp h hax) fun s₃ ha e₃ => ?_
  have k₃ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s₃ := h.call hp ha (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact VG.Proof.Pbkdf2.Md.X86.Iterate.save_hv hp (by omega)
      · exact VG.Proof.Pbkdf2.Md.X86.Iterate.save_cmp hp) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Region.sub_prefix (by omega) a ha)
      · exact VG.Proof.Pbkdf2.Md.X86.Iterate.cmp_sub hp)
  have f := ha.frame
  rw [VG.Proof.Pbkdf2.Md.X86.Iterate.stk_eq h] at f
  exact k s₃ k₃ (f.mono (by simp)) e₃

theorem lc_ok {o : Nat} (ho : o + H.N ≤ 2 * H.S) {m : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s)
    (hpad : bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s' → Frame [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩, VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64) = hO.md.compress
        (hO.md.stateAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 o))
        (hO.md.tailBlock H.D (bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)) →
      bytesAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      bytesAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D → WP isa c s' Q) :
    WP isa (.block (H.loadKey o ++ H.atBlk)) s fun s' => WP isa (.seq H.cmp c) s' Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  rw [← List.append_nil (H.loadKey o ++ H.atBlk)]
  refine VG.Proof.Pbkdf2.Md.X86.Iterate.load_ok hO hp ho h fun s₂ k₂ ax₂ f₁ st₂ => WP.block_nil (WP.seq (VG.Proof.Pbkdf2.Md.X86.Iterate.cmpS_ok hO hp k₂ ax₂ fun s₃ k₃ f₂ e₃ => ?_))
  have dB : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
      ∀ r ∈ [(⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩ : Region)], Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r :=
    fun h₁ h₂ r hr => VG.Proof.Pbkdf2.Md.X86.Iterate.blk_disj hp h₁ h₂ r (by simp only [List.mem_singleton] at hr; simp [hr])
  have pad₂ : bytesAt s₂.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 H.D) (H.B - H.D) =
      hO.md.tailPad H.D := by
    rw [Memory.add_ofNat, Memory.frame_bytesAt f₁ (dB (by omega) (by omega_using [hB64, hDN, hN])) (by omega), hpad, hO.tail]
  have u₂ : bytesAt s₂.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
      bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D :=
    Memory.frame_bytesAt f₁ (dB (by omega) (by omega_using [hB64, hDN, hN])) (by omega)
  have f₃ : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩, VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀] s.mem s₃.mem :=
    (f₁.mono (by simp)).trans f₂
  refine k s₃ k₃ f₃ ?_ ?_ ?_
  · rw [e₃, st₂, Md.blockAt_tailPad (by omega_using [hB64, hDN, hN]) pad₂, u₂]
  · rw [Memory.frame_bytesAt f₃ (VG.Proof.Pbkdf2.Md.X86.Iterate.blk_disj hp (by omega) (by omega)) (by omega), hpad]
  · exact Memory.frame_bytesAt f₃ (VG.Proof.Pbkdf2.Md.X86.Iterate.blk_disj hp (by omega) (by omega)) (by omega)

/-! ## The end of a step: the digest, `T ← T ⊕ U` and the count -/

omit hp in
theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      VG.WriteBytes.writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  refine congrArg (VG.WriteBytes.writeBytes m d) ?_
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

omit hp in
theorem wp_xorm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine VG.Proof.Sha256.X86.Stream.WP.cons
    (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 32) false false).setReg d (s.gpr d ^^^ s.mem.readW a 32))
    ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load32, ha, hin]

omit hp in
/-- `T ← T ⊕ U` for the first `n` words of `T` at `t` (in `edx`) and `U` at
`x + N` (`x` in `ebx`). -/
theorem xor_ok {x t : BitVec 32} (hd : Region.Disjoint ⟨t.setWidth 64, H.D⟩ ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩)
    (fx : x.toNat + H.N + H.D ≤ 2 ^ 32) (ft : t.toNat + H.D ≤ 2 ^ 32) :
    ∀ n, 4 * n ≤ H.D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ebx = x → s.gpr .edx = t →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr t (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (t.setWidth 64)
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (t.setWidth 64) (4 * n))
          (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbx hdx hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbx hdx (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.xorW, List.cons_append, List.nil_append]
    have eU : addr x (H.N + 4 * n) = x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n) := by
      rw [addr_eq (by omega), Memory.add_ofNat]
    have eT : addr t (4 * n) = t.setWidth 64 + BitVec.ofNat 64 (4 * n) := addr_eq (by omega)
    refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr x (H.N + 4 * n)) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, g₁ _ (by decide), hbx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    have hw := hout n (by omega)
    refine VG.Proof.Pbkdf2.Md.X86.Iterate.wp_xorm (a := addr t (4 * n)) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₂.other _ (by decide), g₁ _ (by decide), hdx])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact InRegions.right' hw) fun s₃ u₃ => ?_
    refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr t (4 * n))
      (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hdx])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw) fun s₄ u₄ => k s₄ (fun r hr => by
        rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr]) (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁])
        (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (t.setWidth 64) (4 * n))
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, VG.Proof.Pbkdf2.Md.X86.Iterate.writeW_xor32, m₁, eU, eT,
      bytesAt_writeBytes_sep (p := t.setWidth 64 + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n))]
    · have e := VG.WriteBytes.writeBytes_append s.mem (t.setWidth 64) _ (Spec.Pbkdf2.xorBytes
        (bytesAt s.mem (t.setWidth 64 + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro y h₁ h₂
      rw [hl] at h₂
      exact hd y (by simp only [Region.Contains]; omega) (Memory.off_contains h₁ (by omega) (by omega))
    · omega
    · intro y h₁ h₂
      rw [hl] at h₂
      exact Memory.sep_after h₁ h₂ (by omega)
    · omega

theorem tail_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s)
    (hpad : bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB)
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ (m - 1) s' → s'.zf = some (decide (m - 1 = 0)) →
      Frame [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩, VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀] s.mem s'.mem →
      bytesAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      bytesAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        (hO.md.digest (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64))).take H.D →
      bytesAt s'.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D = Spec.Pbkdf2.xorBytes (bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D)
        ((hO.md.digest (hO.md.stateAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64))).take H.D) → Q s') :
    WP isa (.block (H.digest ++ H.tStep)) s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  have hD4 := hp.hz.D.2.2
  have hvt := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_toNat hp
  have nt := hp.nt
  have hD4' : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  have sbB : Region.Sub ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) :=
    fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  refine VG.Proof.Pbkdf2.Md.X86.digest_ok hp.hz hO.out h.ebx (by omega_using [hvt, hw, hf]) (VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp h.wr) hpad fun s₁ g₁ rd₁ wr₁ f₁ b₁ p₁ => ?_
  have k₁ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s₁ := h.write rd₁ wr₁ g₁ f₁
    ((VG.Proof.Pbkdf2.Md.X86.Iterate.save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))) ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, sbB⟩
  simp only [Hash.tStep, List.cons_append, List.nil_append]
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 3) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, k₁.esp]; rfl) (VG.Proof.Pbkdf2.Md.X86.Iterate.argIn hp k₁.rd k₁.wr (by decide))
    fun s₂ u₂ => ?_
  have dx₂ : s₂.gpr .edx = VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀ := by rw [u₂.gpr, k₁.readArg hp (by decide)]
  have k₂ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s₂ := k₁.write u₂.rd u₂.wr (fun r _ _ h3 => u₂.other r h3) (R := ⟨0, 0⟩)
    (by rw [u₂.mem]; exact Frame.refl _ _) (fun _ _ h => by simp [Region.Contains] at h)
    ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, fun _ h => by simp [Region.Contains] at h⟩
  have hd : Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64, H.D⟩ ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩ :=
    (VG.Proof.Pbkdf2.Md.X86.Iterate.t_blk hp).sub_right (Region.sub_prefix (by omega_using [hB64, hDN, hN]))
  refine VG.Proof.Pbkdf2.Md.X86.Iterate.xor_ok hd (by omega_using [hvt, hB64, hDN, hN, hw, hf]) nt (H.D / 4) (by omega_using []) _ s₂ _ k₂.ebx dx₂
    (fun j hj => by
      rw [addr_eq (by omega)]
      exact InRegions.right' (VG.Proof.Pbkdf2.Md.X86.inReg (VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp k₂.wr) (by omega_using [hj, hB64, hDN, hN]) (by omega)))
    (fun j hj => by
      rw [addr_eq (by omega_using [hj, nt]), k₂.wr]
      exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀, (VG.Proof.Pbkdf2.Md.X86.Iterate.mem_wr hp).2, Offset.contains_base _ (by omega_using [hj]) (by omega)⟩)
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  rw [hD4'] at m₃
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₂.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D)
      (bytesAt s₂.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)).length = H.D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₃ : Frame [VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀] s₂.mem s₃.mem := by
    rw [m₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have k₃ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s₃ := k₂.write rd₃ wr₃ (fun r _ h2 _ => g₃ r h2) f₃
    (hp.t_s.sub_right (VG.Proof.Pbkdf2.Md.X86.Iterate.save_sub hp)).symm ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀, by simp, fun _ h => h⟩
  refine VG.Proof.Sha256.X86.Stream.wp_subi fun s₄ u₄ z₄ => WP.block_nil ?_
  have e₄ : s₃.gpr .edi - 1 = BitVec.ofNat 32 (m - 1) := by
    rw [k₃.edi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.Sha256.X86.Stream.sub_ofNat hm]
  have k₄ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ (m - 1) s₄ :=
    ⟨by rw [u₄.rd, k₃.rd], by rw [u₄.wr, k₃.wr], by rw [u₄.other _ (by decide), k₃.esp],
      by rw [u₄.other _ (by decide), k₃.ebp], by rw [u₄.other _ (by decide), k₃.ebx],
      by rw [u₄.other _ (by decide), k₃.esi], by rw [u₄.gpr, e₄], u₄.mem ▸ k₃.saved, u₄.mem ▸ k₃.frame⟩
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  have tB : ∀ r ∈ [VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀], Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact (VG.Proof.Pbkdf2.Md.X86.Iterate.t_blk hp).symm
  have tB' : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
      ∀ r ∈ [VG.Proof.Pbkdf2.Md.X86.Iterate.tR H s₀], Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h₁ h₂ r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ((VG.Proof.Pbkdf2.Md.X86.Iterate.t_blk hp).sub_right (Offset.sub _ (by omega) (by omega))).symm
  refine k s₄ k₄ (by rw [z₄, e₄, VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega_using [hn])]) ?_ ?_ ?_ ?_
  · rw [u₄.mem]; exact (f₁.mono (by simp)).trans (m₂ ▸ f₃.mono (by simp))
  · rw [u₄.mem, Memory.frame_bytesAt f₃ (tB' (by omega_using []) (by omega_using [hB64, hDN, hN])) (by omega), m₂, p₁]
  · rw [u₄.mem, Memory.frame_bytesAt f₃ (tB' (Nat.le_refl _) (by omega_using [hB64, hDN, hN])) (by omega), m₂, b₁]
  · have hT₁ : bytesAt s₁.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D = bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Md.X86.Iterate.t_blk hp) (by omega)
    rw [u₄.mem, m₃, bytesAt_writeBytes_self' hxl (by omega), m₂, hT₁, b₁]

end

/-! ## A step -/

section
variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀)
include hp

omit hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {r : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.Inv hO sc s₀ (r + 1) s) :
    WP isa H.body s fun s' => VG.X86.eval .ne s' = some (r != 0) ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.Inv hO sc s₀ r s' := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  have hvt := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_toNat hp
  have hlt : r + 1 < 2 ^ 32 := by have h_le := h.le; have := (VG.X86.arg s₀ 2).isLt; simp only [VG.Proof.Pbkdf2.Md.X86.Iterate.nn] at *; omega_using [h_le]
  have sbB : Region.Sub ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) :=
    fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  unfold Hash.body
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86.Iterate.lc_ok hO hp (o := 0) (by omega_using [hS]) h.toKR h.pad fun s₂ k₂ f₂ e₂ p₂ u₂ => ?_)
  refine WP.seq ?_
  rw [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86.digest_ok hp.hz hO.out k₂.ebx (by omega) (VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp k₂.wr) p₂ fun s₃ g₃ rd₃ wr₃ f₃ b₃ p₃ => ?_
  have k₃ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ (r + 1) s₃ := k₂.write rd₃ wr₃ g₃ f₃
    ((VG.Proof.Pbkdf2.Md.X86.Iterate.save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))) ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, sbB⟩
  refine VG.Proof.Pbkdf2.Md.X86.Iterate.lc_ok hO hp (o := H.S) (by omega_using [hS]) k₃ p₃ fun s₅ k₅ f₅ e₅ p₅ u₅ => ?_
  refine VG.Proof.Pbkdf2.Md.X86.Iterate.tail_ok hO hp (m := r + 1) (by omega) hlt k₅ p₅ fun s₈ k₈ z₈ f₈ p₈ b₈ t₈ => ?_
  rw [Nat.add_sub_cancel] at k₈ z₈
  -- `T` is untouched until the end.
  have dT : ∀ {rs : List Region}, (∀ q ∈ rs, Region.Sub q (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) ∨ q = VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀) →
      ∀ q ∈ rs, Region.Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64, H.D⟩ q := by
    intro rs hrs q hq
    rcases hrs q hq with hq | rfl
    · exact hp.t_s.sub_right hq
    · exact hp.b_t.symm
  have sub₁ : ∀ q ∈ [(⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64, H.N⟩ : Region), VG.Proof.Pbkdf2.Md.X86.Iterate.cmpR H s₀, VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀],
      Region.Sub q (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) ∨ q = VG.Proof.Pbkdf2.Md.X86.Iterate.stkR s₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl)
    · exact .inl fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Region.sub_prefix (by omega) a ha)
    · exact .inl (VG.Proof.Pbkdf2.Md.X86.Iterate.cmp_sub hp)
    · exact .inr rfl
  have hT₅ : bytesAt s₅.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D = bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D := by
    rw [Memory.frame_bytesAt f₅ (dT sub₁) (by omega),
      Memory.frame_bytesAt f₃ (dT (by simp only [List.mem_singleton]; rintro q rfl; exact .inl sbB)) (by omega),
      Memory.frame_bytesAt f₂ (dT sub₁) (by omega)]
  rw [hT₅, e₅, b₃, e₂, show (VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 0 = (VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 by simp] at t₈
  rw [e₅, b₃, e₂, show (VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 0 = (VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 by simp] at b₈
  refine ⟨?_, { k₈ with pad := p₈, le := by have h_le := h.le; omega, val := ?_ }⟩
  · rw [VG.Proof.Sha256.X86.Stream.eval_ne, z₈, Option.map_some]
    cases r <;> rfl
  · rw [h.val, VG.Proof.Pbkdf2.Md.X86.Iterate.iterate_succ, b₈, t₈]; rfl

theorem loop_ok {n : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.Inv hO sc s₀ n s) (hz' : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop H.body .ne)) s (VG.Proof.Pbkdf2.Md.X86.Iterate.Inv hO sc s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show s.zf = _; exact hz') (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => VG.Proof.Pbkdf2.Md.X86.Iterate.Inv hO sc s₀ (m + 1) s)
      (fun m s hs' => WP.mono (VG.Proof.Pbkdf2.Md.X86.Iterate.body_ok hO hp hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end

/-! ## The prologue and the epilogue -/

section
variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀)
include hp

theorem pro_ok : WP isa (.block H.prologue) s₀ fun s => VG.Proof.Pbkdf2.Md.X86.Iterate.Inv hO sc s₀ (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀) s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ = 0)) := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  obtain ⟨sR, tR'⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.mem_wr hp
  have hvt := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_toNat hp
  have hD4 := hp.hz.D.2.2
  have hD4' : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  have tl := hp.hz.tail_length
  have nu := hp.nu; have nt := hp.nt
  have dA : ∀ r ∈ [saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)], (VG.Proof.Pbkdf2.Md.X86.Iterate.argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (VG.Proof.Pbkdf2.Md.X86.Iterate.save_sub hp)
  simp only [Hash.prologue, List.append_assoc, List.singleton_append]
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 4) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at]; rfl) (VG.Proof.Pbkdf2.Md.X86.Iterate.argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Stream.X86.save_ok H.st (scr := VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega_using [hf, hb]) (by omega)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (VG.Proof.Pbkdf2.Stream.X86.arg_sub rfl (by omega_using [hi]) (by have hp_spf := hp.spf; omega))) (by decide)
  have i₂ : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.Pbkdf2.Md.X86.Iterate.argIn hp rfl rfl hi
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 0) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 2) (by
      rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 2 (by decide)) fun s₅ u₅ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₆ u₆ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₇ u₇ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 1) (by
      rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide))
    fun s₈ u₈ => ?_
  have m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have bp₈ : s₈.gpr .ebp = VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl
  have bx₈ : s₈.gpr .ebx = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]
    rfl
  have si₈ : s₈.gpr .esi = VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.mem, rA 0 (by decide)]
  have di₈ : s₈.gpr .edi = VG.X86.arg s₀ 2 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem,
      rA 2 (by decide)]
  have dx₈ : s₈.gpr .edx = VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀ := by
    rw [u₈.gpr, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, rA 1 (by decide)]
  have sp₈ : s₈.gpr .esp = VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
  have ucov : Covers [VG.Proof.Pbkdf2.Md.X86.Iterate.uR H s₀] (s₈.rd ++ s₈.wr) := covers_one (by rw [rd₈, hp.rd]; simp)
  -- `U` into the block.
  refine VG.Proof.Pbkdf2.Md.X86.copyW_ok (by decide) (by decide) (H.D / 4) _ s₈ _ dx₈ bx₈ (by omega_using [nu]) (by omega)
    (fun j hj => by
      rw [addr_eq (by omega_using [hj, nu])]; have := VG.Proof.Pbkdf2.Md.X86.inReg (o := 4 * j) (n := 4) ucov (by omega_using [hj]) (by omega)
      rwa [show 0 + 4 * j = 4 * j by omega_using []])
    (fun j hj => by rw [addr_eq (by omega)]; exact VG.Proof.Pbkdf2.Md.X86.inReg (VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp wr₈) (by omega_using [hj, hB64, hDN, hN]) (by omega)) ?_
    fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  · rw [hD4', BitVec.add_zero]
    exact hp.u_s.sep (Region.contains_self _ _)
      (by rw [VG.Proof.Pbkdf2.Md.X86.Iterate.hv_eq hp, Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hB64, hDN, hN, hf]) (by omega_using [hw, hf]))
  rw [hD4', BitVec.add_zero] at m₉
  -- The padding.
  refine VG.Proof.Pbkdf2.Md.X86.pad_ok hp.hz (s := s₉) (x := VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀) (by rw [g₉ _ (by decide), bx₈]) (by omega_using [hvt, hw, hf]) (VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp (wr₉.trans wr₈))
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_test fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  have m₁₁ : s₁₁.mem = VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes s₂.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N)
      (bytesAt s₂.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64) H.D)) ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB := by
    rw [u₁₁.mem, m₁₀, m₉, m₈]
  have gr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁₁.gpr r = s₈.gpr r := fun r _ h2 _ => by
    rw [u₁₁.gpr, g₁₀ r h2, g₉ r h2]
  have fB : Frame [⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₂.mem s₁₁.mem := by
    rw [m₁₁]
    refine (VG.WriteBytes.writeBytes_frame _ _ _ ?_).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]
      have := Offset.contains_base ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (k := H.B)
        (by omega_using [hB64, hDN, hN]) (by omega)
      rwa [BitVec.add_zero] at this
    · rw [tl, ← Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hB64, hDN, hN]) (by omega)
  have sbB : Region.Sub ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) :=
    fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  have dsB : (saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀)).Disjoint ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ :=
    (VG.Proof.Pbkdf2.Md.X86.Iterate.save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))
  have sv : SavedRegs H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀) s₀ s₁₁.mem :=
    (sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)).frame H.st fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dsB)
  have fr : Frame (VG.Proof.Pbkdf2.Md.X86.Iterate.wrs H sc s₀) s₀.mem s₁₁.mem :=
    (f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.X86.Iterate.save_sub hp⟩).trans
    (fB.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, sbB⟩)
  have edi : s₁₁.gpr .edi = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀) := by
    rw [gr _ (by decide) (by decide) (by decide), di₈, VG.Proof.Pbkdf2.Md.X86.Iterate.nn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have dU : Mem.Sep ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D
      ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB.length := by
    rw [tl, ← Memory.add_ofNat]
    have := Offset.sep ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (e := H.D)
      (k := H.B - H.D) (.inl (by omega)) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine ⟨⟨⟨by rw [u₁₁.rd, rd₁₀, rd₉, rd₈], by rw [u₁₁.wr, wr₁₀, wr₉, wr₈],
    by rw [gr _ (by decide) (by decide) (by decide), sp₈], by rw [gr _ (by decide) (by decide) (by decide), bp₈],
    by rw [gr _ (by decide) (by decide) (by decide), bx₈], by rw [gr _ (by decide) (by decide) (by decide), si₈],
    edi, sv, fr⟩, ?_, Nat.le_refl _, ?_⟩, ?_⟩
  · rw [m₁₁, ← tl, bytesAt_writeBytes_self' rfl (by omega)]
  · -- `U` and `T`.
    have hU₂ : bytesAt s₂.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64) H.D = bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt f₂' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.u_s.sub_right (VG.Proof.Pbkdf2.Md.X86.Iterate.save_sub hp)) (by omega)
    have hU : bytesAt s₁₁.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64) H.D := by
      rw [m₁₁, bytesAt_writeBytes_sep _ _ dU (by omega), bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega),
        hU₂]
    have hT : bytesAt s₁₁.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D = bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt ((f₂'.mono (rs' := [saveR H.st (VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀), ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩])
        (by simp)).trans (fB.mono (by simp))) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.t_s.sub_right (VG.Proof.Pbkdf2.Md.X86.Iterate.save_sub hp)
        · exact VG.Proof.Pbkdf2.Md.X86.Iterate.t_blk hp) (by omega)
    rw [hU, hT]
  · rw [z₁₁, g₁₀ _ (by decide), g₉ _ (by decide), di₈, test_z]

omit hp in
/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {m : Mem}
    (hT : bytesAt m ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D = Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.Md.X86.Iterate.stepM hO s₀) (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀)
      (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64) H.D) (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) H.D))
    {k0 : List Byte} (hk : k0.length = hO.hH.SH.H.blockSize)
    (hi : hO.hH.SH.Repr s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64) (xorPad k0 ipad))
    (ho : hO.hH.SH.Repr s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.key s₀).setWidth 64 + BitVec.ofNat 64 hO.hH.SH.stateBytes) (xorPad k0 opad)) :
    bytesAt m ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) hO.hH.SH.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey hO.hH.SH.H k0) (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀) (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.up s₀).setWidth 64) hO.hH.SH.digestBytes)
        (bytesAt s₀.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.tp s₀).setWidth 64) hO.hH.SH.digestBytes) := by
  have hl := hO.link
  have hB : 0 < H.B := by have hl_DL := hl.DL; omega
  rw [hl.hB] at hk
  rw [hl.hS, ← hO.sizes.S] at ho
  have li : (xorPad k0 ipad).length = H.B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = H.B := by simp [xorPad, hk]
  have ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  have eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length _ hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem epilogue_ok {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.Inv hO sc s₀ 0 s) :
    WP isa (.block H.st.restore) s fun s' => abiPreserved s₀ s' ∧ (iterG hO.hH.SH sc).post s₀ s' := by
  obtain ⟨hb, hf, hw, -⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  refine WP.mono (VG.Proof.Pbkdf2.Stream.X86.restore_ok H.st h.ebp h.saved (by rw [h.wr]; exact (VG.Proof.Pbkdf2.Md.X86.Iterate.mem_wr hp).1) (by omega_using [hf, hb]) hp.nw)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact h.toKR.ret hp⟩, fun k0 hk hi ho' => ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), h.esp]
    · exact hg r (callee_saved r hr he)
  · rw [hm]; exact VG.Proof.Pbkdf2.Md.X86.Iterate.post_eq hO h.val.symm hk hi ho'

theorem correct : WP isa H.iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hO.hH.SH sc).post s₀ s' := by
  unfold Hash.iterate
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.Iterate.pro_ok hO hp) fun s₁ ⟨h, hz'⟩ => ?_)
  exact WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86.Iterate.loop_ok hO hp h hz') fun s₂ h₂ => VG.Proof.Pbkdf2.Md.X86.Iterate.epilogue_ok hO hp h₂)

end

end VG.Proof.Pbkdf2.Md.X86.Iterate

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.IterateCT`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86 (32-bit): constant time

As for HMAC's `init` (`HmacInitCT.lean`): the pieces between the calls are
checked by the taint analysis, those that read the arguments on the stack (the
prologue, and the end of a step, which loads `t`) with the arguments public
(`argTaint`); the calls of the compression function are related by `cmp_rel`,
from its contract. Then `iterate` is verified against the contract with the
arguments read only (`iterG`), and with them writable (`iterW`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (HashOK iterG iterW argTaint ArgsOut agree_argTaint rel_agree rel_wp stk)
open VG.Proof.Sha256.X86.Stream (eval_e eval_ne)
open Spec.Sha256 (bytesAt)

/-- The registers `KR` fixes. -/
abbrev pubRegs : List Reg := [.esp, .ebp, .ebx, .esi, .edi]

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block H.prologue) hc).isSome = true
  load : ∃ hc, (VG.Taint.check taint (τr VG.Proof.Pbkdf2.Md.X86.Iterate.pubRegs) (.block (H.loadKey 0 ++ H.atBlk)) hc).isSome = true
  mid : ∃ hc, (VG.Taint.check taint (τr VG.Proof.Pbkdf2.Md.X86.Iterate.pubRegs) (.block (H.digest ++ H.loadKey H.S ++ H.atBlk)) hc).isSome = true
  tail : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .esi, .edi] (4 + 4 * 5))
    (.block (H.digest ++ H.tStep)) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.st.restore) hc).isSome = true

theorem skip_check : ∃ hc, (VG.Taint.check taint (τr []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, VG.X86.arg s₀ i = VG.X86.arg s₀' i

/-- What the pieces keep, and the padding. -/
structure KP (H : Hash) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop extends VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s where
  pad : bytesAt s.mem ((VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB

/-! ## Each piece, in one run -/

section
variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀)
include hO hp

theorem b1_ok {m : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m s) :
    WP isa (.block (H.loadKey 0 ++ H.atBlk)) s fun t =>
      VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m t ∧ t.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ + BitVec.ofNat 32 H.N := by
  rw [← List.append_nil (H.loadKey 0 ++ H.atBlk)]
  have := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  refine VG.Proof.Pbkdf2.Md.X86.Iterate.load_ok hO hp (by have := hp.hz.S; omega) h.toKR fun s₂ k₂ ax₂ f₁ _ => WP.block_nil ⟨⟨k₂, ?_⟩, ax₂⟩
  rw [Memory.frame_bytesAt f₁ (fun r hr => VG.Proof.Pbkdf2.Md.X86.Iterate.blk_disj hp (by omega) (by omega) r (by
    simp only [List.mem_singleton] at hr; simp [hr])) (by omega), h.pad]

theorem c_ok {m : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m s) (hax : s.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ + BitVec.ofNat 32 H.N) :
    WP isa H.cmp s (VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m) := by
  have := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  refine VG.Proof.Pbkdf2.Md.X86.Iterate.cmpS_ok hO hp h.toKR hax fun s₃ k₃ f₃ _ => ⟨k₃, ?_⟩
  rw [Memory.frame_bytesAt f₃ (VG.Proof.Pbkdf2.Md.X86.Iterate.blk_disj hp (by omega) (by omega)) (by omega), h.pad]

theorem b2_ok {m : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m s) :
    WP isa (.block (H.digest ++ H.loadKey H.S ++ H.atBlk)) s fun t =>
      VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m t ∧ t.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ + BitVec.ofNat 32 H.N := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.bounds hp
  have := VG.Proof.Pbkdf2.Md.X86.Iterate.hv_toNat hp; have := hp.hz.DL
  have sbB : Region.Sub ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀) :=
    fun a ha => VG.Proof.Pbkdf2.Md.X86.Iterate.hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  rw [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86.digest_ok hp.hz hO.out h.ebx (by omega) (VG.Proof.Pbkdf2.Md.X86.Iterate.cov_hv hp h.wr) h.pad fun s₃ g₃ rd₃ wr₃ f₃ _ p₃ => ?_
  have k₃ : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s₃ := h.toKR.write rd₃ wr₃ g₃ f₃
    ((VG.Proof.Pbkdf2.Md.X86.Iterate.save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))) ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.scR sc s₀, by simp, sbB⟩
  rw [← List.append_nil (H.loadKey H.S ++ H.atBlk)]
  refine VG.Proof.Pbkdf2.Md.X86.Iterate.load_ok hO hp (by omega) k₃ fun s₂ k₂ ax₂ f₁ _ => WP.block_nil ⟨⟨k₂, ?_⟩, ax₂⟩
  rw [Memory.frame_bytesAt f₁ (fun r hr => VG.Proof.Pbkdf2.Md.X86.Iterate.blk_disj hp (by omega) (by omega) r (by
    simp only [List.mem_singleton] at hr; simp [hr])) (by omega), p₃]

theorem b3_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m s) :
    WP isa (.block (H.digest ++ H.tStep)) s fun t => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ (m - 1) t ∧ t.zf = some (decide (m - 1 = 0)) :=
  VG.Proof.Pbkdf2.Md.X86.Iterate.tail_ok hO hp hm hn h.toKR h.pad fun _ k z _ p _ _ => ⟨⟨k, p⟩, z⟩

end

/-! ## Two runs -/

variable {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat}
variable {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀) (hp' : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc s₀') (hq : VG.Proof.Pbkdf2.Md.X86.Iterate.PubEq s₀ s₀')

theorem PubEq.nn (hq : VG.Proof.Pbkdf2.Md.X86.Iterate.PubEq s₀ s₀') : VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ = VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀' := by
  show (VG.X86.arg s₀ 2).toNat = (VG.X86.arg s₀' 2).toNat; rw [hq.args 2 (by decide)]

theorem eqs (hq : VG.Proof.Pbkdf2.Md.X86.Iterate.PubEq s₀ s₀') : VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀' = VG.Proof.Pbkdf2.Md.X86.Iterate.scr s₀ ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀' = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ :=
  ⟨(hq.args 4 (by decide)).symm, by rw [VG.Proof.Pbkdf2.Md.X86.Iterate.hv, VG.Proof.Pbkdf2.Md.X86.Iterate.hv, VG.Proof.Pbkdf2.Md.X86.Iterate.scr, VG.Proof.Pbkdf2.Md.X86.Iterate.scr, hq.args 4 (by decide)]⟩

theorem kr_agree (hq : VG.Proof.Pbkdf2.Md.X86.Iterate.PubEq s₀ s₀') {m : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀ m s)
    (h' : VG.Proof.Pbkdf2.Md.X86.Iterate.KR H sc s₀' m s') : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86.Iterate.pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp, VG.Proof.Pbkdf2.Md.X86.Iterate.E, VG.Proof.Pbkdf2.Md.X86.Iterate.E, hq.esp]
  · rw [h.ebp, h'.ebp, (VG.Proof.Pbkdf2.Md.X86.Iterate.eqs (H := H) hq).1]
  · rw [h.ebx, h'.ebx, (VG.Proof.Pbkdf2.Md.X86.Iterate.eqs (H := H) hq).2]
  · rw [h.esi, h'.esi, VG.Proof.Pbkdf2.Md.X86.Iterate.key, VG.Proof.Pbkdf2.Md.X86.Iterate.key, hq.args 0 (by decide)]
  · rw [h.edi, h'.edi]

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : VG.Proof.Pbkdf2.Md.X86.Iterate.Pre H sc t) {s : State} (hsp : s.gpr .esp = VG.Proof.Pbkdf2.Md.X86.Iterate.E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(VG.Proof.Pbkdf2.Md.X86.Iterate.E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_t h.a_t
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.a_s

include hO hp hp' hq

/-- A call of the compression function, in both runs. -/
theorem cmp_rel' {m : Nat} :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m s ∧ s.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀ + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' m s' ∧ s'.gpr .eax = VG.Proof.Pbkdf2.Md.X86.Iterate.hv H s₀' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m s ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' m s' := by
  obtain ⟨e4, ehv⟩ := VG.Proof.Pbkdf2.Md.X86.Iterate.eqs (H := H) hq
  have hB : 0 < H.B := by have := hp.hz.B4; omega
  exact rel_wp (VG.Proof.Pbkdf2.Md.X86.cmp_rel hO.comp hB (sp := VG.Proof.Pbkdf2.Md.X86.Iterate.E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
      ⟨VG.Proof.Pbkdf2.Md.X86.Iterate.cmpArgs hp k.toKR a, by have := VG.Proof.Pbkdf2.Md.X86.Iterate.cmpArgs hp' k'.toKR a'; rwa [e4, ehv] at this, k.esp,
        by rw [k'.esp, VG.Proof.Pbkdf2.Md.X86.Iterate.E, VG.Proof.Pbkdf2.Md.X86.Iterate.E, hq.esp]⟩)
    (fun _ ⟨k, a⟩ => VG.Proof.Pbkdf2.Md.X86.Iterate.c_ok hO hp k a) (fun _ ⟨k, a⟩ => VG.Proof.Pbkdf2.Md.X86.Iterate.c_ok hO hp' k a)

theorem body_rel (hc : VG.Proof.Pbkdf2.Md.X86.Iterate.Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m s ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' m s') H.body
      fun s s' => (VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ (m - 1) s ∧ s.zf = some (decide (m - 1 = 0))) ∧
        (VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' (m - 1) s' ∧ s'.zf = some (decide (m - 1 = 0))) := by
  have b1 := rel_agree (F := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m) (F' := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' m) (τr VG.Proof.Pbkdf2.Md.X86.Iterate.pubRegs) (fun _ _ h h' => agree_regs (VG.Proof.Pbkdf2.Md.X86.Iterate.kr_agree hq h.toKR h'.toKR)) hc.load
    (fun _ h => VG.Proof.Pbkdf2.Md.X86.Iterate.b1_ok hO hp h) (fun _ h => VG.Proof.Pbkdf2.Md.X86.Iterate.b1_ok hO hp' h)
  have b2 := rel_agree (F := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m) (F' := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' m) (τr VG.Proof.Pbkdf2.Md.X86.Iterate.pubRegs) (fun _ _ h h' => agree_regs (VG.Proof.Pbkdf2.Md.X86.Iterate.kr_agree hq h.toKR h'.toKR)) hc.mid
    (fun _ h => VG.Proof.Pbkdf2.Md.X86.Iterate.b2_ok hO hp h) (fun _ h => VG.Proof.Pbkdf2.Md.X86.Iterate.b2_ok hO hp' h)
  have b3 := rel_agree (F := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ m) (F' := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' m) (argTaint [.ebp, .ebx, .esi, .edi] (4 + 4 * 5)) (fun s s' k k' =>
      agree_argTaint (fun r hr => VG.Proof.Pbkdf2.Md.X86.Iterate.kr_agree hq k.toKR k'.toKR r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind))
        (VG.Proof.Pbkdf2.Md.X86.Iterate.kr_agree hq k.toKR k'.toKR .esp (by simp)) (VG.Proof.Pbkdf2.Md.X86.Iterate.args_out hp k.esp k.wr) (VG.Proof.Pbkdf2.Md.X86.Iterate.args_out hp' k'.esp k'.wr)
        fun j hj => by rw [k.toKR.argEq hp hj, k'.toKR.argEq hp' hj, hq.args j hj]) hc.tail
    (fun _ h => VG.Proof.Pbkdf2.Md.X86.Iterate.b3_ok hO hp hm hn h) (fun _ h => VG.Proof.Pbkdf2.Md.X86.Iterate.b3_ok hO hp' hm hn h)
  exact b1.seq ((VG.Proof.Pbkdf2.Md.X86.Iterate.cmp_rel' hO hp hp' hq).seq (b2.seq ((VG.Proof.Pbkdf2.Md.X86.Iterate.cmp_rel' hO hp hp' hq).seq b3)))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ n s ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' n s'

theorem step_rel (hc : VG.Proof.Pbkdf2.Md.X86.Iterate.Checks H) (n : Nat) :
    RelCT isa (VG.Proof.Pbkdf2.Md.X86.Iterate.LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') n) H.body fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ 0 s ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' 0 s') ∧
      (isa.eval .ne s = some true → ∃ m < n, VG.Proof.Pbkdf2.Md.X86.Iterate.LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt : VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ < 2 ^ 32 := (VG.X86.arg s₀ 2).isLt
  by_cases hn : 1 ≤ n ∧ n ≤ VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀
  · refine ((VG.Proof.Pbkdf2.Md.X86.Iterate.body_rel hO hp hp' hq hc hn.1 (by omega)).mono
      (P' := VG.Proof.Pbkdf2.Md.X86.Iterate.LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') n) (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
      fun _ _ h => h).mono (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e : isa.eval .ne t = some (!decide (n - 1 = 0)) := by show VG.X86.eval .ne t = _; rw [VG.Proof.Sha256.X86.Stream.eval_ne, z]; rfl
    have e' : isa.eval .ne t' = some (!decide (n - 1 = 0)) := by show VG.X86.eval .ne t' = _; rw [VG.Proof.Sha256.X86.Stream.eval_ne, z']; rfl
    rw [e, e']
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : n - 1 = 0 := by simpa using hf
      exact ⟨hl ▸ i, hl ▸ i'⟩
    · have hl : n - 1 ≠ 0 := by simpa using ht
      exact ⟨n - 1, by omega, by omega, by omega, i, i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel (hc : VG.Proof.Pbkdf2.Md.X86.Iterate.Checks H) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀) s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ = 0))) ∧
        (VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀') s' ∧ s'.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀' = 0))))
      (.ite .e (.block []) (.loop H.body .ne))
      fun s s' => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ 0 s ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' 0 s' := by
  have hN := hq.nn
  have ev : ∀ {t : State} {k : Nat}, t.zf = some (decide (k = 0)) → isa.eval .e t = some (decide (k = 0)) :=
    fun h => by show VG.X86.eval .e _ = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hN]) ?_ ?_
  · by_cases e : VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ = 0
    · have e' : VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀' = 0 := hN ▸ e
      exact (rel_agree (c := .block [])
        (F := fun s => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀) s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ = 0)))
        (F' := fun s => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀') s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀' = 0)))
        (G := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ 0) (G' := VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' 0) (τr [])
        (fun s s' h h' => agree_regs (by simp)) VG.Proof.Pbkdf2.Md.X86.Iterate.skip_check
        (fun s h => WP.block_nil (e ▸ h.1)) (fun s h => WP.block_nil (e' ▸ h.1))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (VG.Proof.Pbkdf2.Md.X86.Iterate.LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀'))
      (VG.Proof.Pbkdf2.Md.X86.Iterate.step_rel hO hp hp' hq hc) (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ ≠ 0 := by simpa using z
    exact ⟨by omega, Nat.le_refl _, h.1.1.1, hN ▸ h.1.2.1⟩

theorem ct (hc : VG.Proof.Pbkdf2.Md.X86.Iterate.Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.iterate fun _ _ => True := by
  have hN := hq.nn
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀) s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀ = 0)))
    (G' := fun s => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀') s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.Md.X86.Iterate.nn s₀' = 0)))
    (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (VG.Proof.Pbkdf2.Md.X86.Iterate.args_out hp rfl rfl) (VG.Proof.Pbkdf2.Md.X86.Iterate.args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.X86.Iterate.pro_ok hO hp) fun _ ⟨h, z⟩ => ⟨⟨h.toKR, h.pad⟩, z⟩)
    (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.X86.Iterate.pro_ok hO hp') fun _ ⟨h, z⟩ => ⟨⟨h.toKR, h.pad⟩, z⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀ 0 s ∧ VG.Proof.Pbkdf2.Md.X86.Iterate.KP H sc s₀' 0 s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Pbkdf2.Md.X86.Iterate.kr_agree hq h.1.toKR h.2.toKR .ebp (by simp)) hr
  exact pro.seq ((VG.Proof.Pbkdf2.Md.X86.Iterate.loop_rel hO hp hp' hq hc).seq restore)

end VG.Proof.Pbkdf2.Md.X86.Iterate

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (iterG iterW)

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.Iterate.Checks H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) (hsat : ∃ s, (iterG hO.hH.SH sc).pre s) :
    Verified X86.target H.iterate (iterG hO.hH.SH sc) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Md.X86.Iterate.correct hO (VG.Proof.Pbkdf2.Md.X86.Iterate.pre_of hO.hH hs hO.sizes hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (VG.Proof.Pbkdf2.Md.X86.Iterate.ct hO (VG.Proof.Pbkdf2.Md.X86.Iterate.pre_of hO.hH h₁ hO.sizes hfit) (VG.Proof.Pbkdf2.Md.X86.Iterate.pre_of hO.hH h₂ hO.sizes hfit) ⟨h1, h2⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `iterate` reads and writes, of those `iterW` gives it. -/
def narrowRd (S D : Nat) (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, 2 * S⟩, ⟨(VG.X86.arg s 1).setWidth 64, D⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (D sc : Nat) (s : State) : List Region :=
  [⟨(VG.X86.arg s 3).setWidth 64, D⟩, ⟨(VG.X86.arg s 4).setWidth 64, 8 * sc⟩]

/-- `iterate` is verified against `iterW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : VG.Proof.Pbkdf2.Md.X86.MdOk H) {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86.Iterate.Checks H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) (hsat : ∃ s, (iterW hO.hH.SH sc).pre s) :
    Verified X86.target H.iterate (iterW hO.hH.SH sc) := by
  have pre : ∀ s, (iterW hO.hH.SH sc).pre s → (iterG hO.hH.SH sc).pre
      (s.withRegions (VG.Proof.Pbkdf2.Md.X86.Iterate.narrowRd hO.hH.SH.stateBytes hO.hH.SH.digestBytes s) (VG.Proof.Pbkdf2.Md.X86.Iterate.narrowWr hO.hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
    simp only [iterG, VG.Proof.Pbkdf2.Md.X86.Iterate.narrowRd, VG.Proof.Pbkdf2.Md.X86.Iterate.narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  refine Verified.narrowTo (VG.Proof.Pbkdf2.Md.X86.Iterate.verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (VG.Proof.Pbkdf2.Md.X86.Iterate.narrowRd hO.hH.SH.stateBytes hO.hH.SH.digestBytes) (VG.Proof.Pbkdf2.Md.X86.Iterate.narrowWr hO.hH.SH.digestBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Pbkdf2.Md.X86.Iterate.narrowRd, VG.Proof.Pbkdf2.Md.X86.Iterate.narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Pbkdf2.Md.X86.Iterate.narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩

end VG.Proof.Pbkdf2.Md.X86.Iterate

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances`. -/
section

/-!
# HMAC's `init` and `finalize` and PBKDF2's `iterate` on x86 (32-bit): the instances

The generic proofs (`IterateCT.lean`, `HmacInitCT.lean`, `HmacFinCT.lean`) at
each hash function of `Hashes.lean`, with the taint checks of their blocks,
which the kernel evaluates for each hash function, moved to the shared
contracts of `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`
(`sig_implies`), which the artifacts are emitted with.
-/

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

/-- Memory holding the arguments `0x1000, 0x1400, 0, 0x1800, 0x2000` of
`iterate` at `0x6004`. -/
def iterMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x6011 then 0x18 else
  if a = 0x6015 then 0x20 else 0

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space, with the arguments
writable. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Pbkdf2.Md.X86.Instances.iterMem
  rd := [⟨0x1000, 2 * S⟩, ⟨0x1400, D⟩]
  wr := [⟨0x1800, D⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 20⟩]

theorem iterSat_args (S D sc : Nat) :
    arg (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) 0 = 0x1000 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) 1 = 0x1400 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) 2 = 0 ∧
      arg (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) 3 = 0x1800 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) 4 = 0x2000 ∧ argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) 0 = 0x6004 ∧
      (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) i = arg (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat 0 0 0) i := fun _ => rfl
  have e' : argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat S D sc) 0 = argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.iterSat 0 0 0) 0 := rfl
  rw [e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-- Memory holding the arguments `0x1000, 0x1400, 0, 0, 0x1800, 0x2000` of
`finalize` at `0x6004`. -/
def finMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x6015 then 0x18 else
  if a = 0x6019 then 0x20 else 0

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space, with the arguments
writable. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Pbkdf2.Md.X86.Instances.finMem
  rd := [⟨0x1400, S⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1800, D⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 24⟩]

theorem finSat_args (S D sc : Nat) :
    arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 0 = 0x1000 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 1 = 0x1400 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 2 = 0 ∧
      arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 3 = 0 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 4 = 0x1800 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 5 = 0x2000 ∧
      argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 0 = 0x6004 ∧ (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) i = arg (VG.Proof.Pbkdf2.Md.X86.Instances.finSat 0 0 0) i := fun _ => rfl
  have e' : argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.finSat S D sc) 0 = argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.finSat 0 0 0) 0 := rfl
  rw [e, e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-- Memory holding the arguments `0x1000, 0x1400, 0x1800, 0, 0x2000` of
`init` at `0x6004`. -/
def initMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x600D then 0x18 else
  if a = 0x6015 then 0x20 else 0

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and an empty key), with the arguments writable. -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Pbkdf2.Md.X86.Instances.initMem
  rd := [⟨0x1800, 0⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1400, S⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 20⟩]

theorem initSat_args (S sc : Nat) :
    arg (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) 0 = 0x1000 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) 1 = 0x1400 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) 2 = 0x1800 ∧
      arg (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) 3 = 0 ∧ arg (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) 4 = 0x2000 ∧ argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) 0 = 0x6004 ∧
      (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) i = arg (VG.Proof.Pbkdf2.Md.X86.Instances.initSat 0 0) i := fun _ => rfl
  have e' : argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.initSat S sc) 0 = argAddr (VG.Proof.Pbkdf2.Md.X86.Instances.initSat 0 0) 0 := rfl
  rw [e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-! ## MD5 -/

theorem md5_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.X86.md5M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem md5_finChecks : HmacFin.Checks VG.Proof.Pbkdf2.Md.X86.md5M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem md5_iterImp : (iterW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.iterSat_args 80 16 48
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using VG.Proof.Pbkdf2.Md.X86.Instances.iterSat 80 16 48

theorem md5_finImp : (finW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.finSat_args 80 16 48
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using VG.Proof.Pbkdf2.Md.X86.Instances.finSat 80 16 48

theorem md5_iterate : Verified X86.target md5M.iterate (Spec.Hmac.md5I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW VG.Proof.Pbkdf2.Md.X86.md5Ok VG.Proof.Pbkdf2.Md.X86.Instances.md5_iterChecks (by decide) md5_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.md5_iterImp

theorem md5_finalize : Verified X86.target md5M.hmacFin (Spec.Hmac.md5I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW VG.Proof.Pbkdf2.Md.X86.md5Ok VG.Proof.Pbkdf2.Md.X86.Instances.md5_finChecks (by decide) md5_finImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.md5_finImp

theorem md5_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.X86.md5M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem md5_initImp : (initW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.initSat_args 80 48
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using VG.Proof.Pbkdf2.Md.X86.Instances.initSat 80 48

theorem md5_init : Verified X86.target md5M.hmacInit (Spec.Hmac.md5I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW VG.Proof.Pbkdf2.Md.X86.md5Ok VG.Proof.Pbkdf2.Md.X86.Instances.md5_initChecks (by decide) md5_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.md5_initImp

/-! ## SHA-384 -/

theorem sha384_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.X86.sha384M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha384_finChecks : HmacFin.Checks VG.Proof.Pbkdf2.Md.X86.sha384M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha384_iterImp : (iterW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.iterSat_args 192 48 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using VG.Proof.Pbkdf2.Md.X86.Instances.iterSat 192 48 234

theorem sha384_finImp : (finW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.finSat_args 192 48 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using VG.Proof.Pbkdf2.Md.X86.Instances.finSat 192 48 234

theorem sha384_iterate : Verified X86.target sha384M.iterate (Spec.Hmac.sha384I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW VG.Proof.Pbkdf2.Md.X86.sha384Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha384_iterChecks (by decide) sha384_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha384_iterImp

theorem sha384_finalize : Verified X86.target sha384M.hmacFin (Spec.Hmac.sha384I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW VG.Proof.Pbkdf2.Md.X86.sha384Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha384_finChecks (by decide) sha384_finImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha384_finImp

theorem sha384_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.X86.sha384M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha384_initImp : (initW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using VG.Proof.Pbkdf2.Md.X86.Instances.initSat 192 234

theorem sha384_init : Verified X86.target sha384M.hmacInit (Spec.Hmac.sha384I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW VG.Proof.Pbkdf2.Md.X86.sha384Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha384_initChecks (by decide) sha384_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha384_initImp

/-! ## SHA-512 -/

theorem sha512_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.X86.sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_finChecks : HmacFin.Checks VG.Proof.Pbkdf2.Md.X86.sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_iterImp : (iterW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.iterSat_args 192 64 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using VG.Proof.Pbkdf2.Md.X86.Instances.iterSat 192 64 234

theorem sha512_finImp : (finW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.finSat_args 192 64 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using VG.Proof.Pbkdf2.Md.X86.Instances.finSat 192 64 234

theorem sha512_iterate : Verified X86.target sha512M'.iterate (Spec.Hmac.sha512I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512Ok' VG.Proof.Pbkdf2.Md.X86.Instances.sha512_iterChecks (by decide) sha512_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_iterImp

theorem sha512_finalize : Verified X86.target sha512M'.hmacFin (Spec.Hmac.sha512I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512Ok' VG.Proof.Pbkdf2.Md.X86.Instances.sha512_finChecks (by decide) sha512_finImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_finImp

theorem sha512_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.X86.sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_initImp : (initW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using VG.Proof.Pbkdf2.Md.X86.Instances.initSat 192 234

theorem sha512_init : Verified X86.target sha512M'.hmacInit (Spec.Hmac.sha512I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512Ok' VG.Proof.Pbkdf2.Md.X86.Instances.sha512_initChecks (by decide) sha512_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_initImp

/-! ## SHA-512/224 -/

theorem sha512_224_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.X86.sha512_224M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_224_finChecks : HmacFin.Checks VG.Proof.Pbkdf2.Md.X86.sha512_224M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_224_iterImp : (iterW Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.iterSat_args 192 28 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using VG.Proof.Pbkdf2.Md.X86.Instances.iterSat 192 28 234

theorem sha512_224_finImp : (finW Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.finSat_args 192 28 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using VG.Proof.Pbkdf2.Md.X86.Instances.finSat 192 28 234

theorem sha512_224_iterate : Verified X86.target sha512_224M.iterate (Spec.Hmac.sha512_224I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512_224Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha512_224_iterChecks (by decide) sha512_224_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_224_iterImp

theorem sha512_224_finalize : Verified X86.target sha512_224M.hmacFin (Spec.Hmac.sha512_224I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512_224Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha512_224_finChecks (by decide) sha512_224_finImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_224_finImp

theorem sha512_224_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.X86.sha512_224M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_224_initImp : (initW Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using VG.Proof.Pbkdf2.Md.X86.Instances.initSat 192 234

theorem sha512_224_init : Verified X86.target sha512_224M.hmacInit (Spec.Hmac.sha512_224I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512_224Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha512_224_initChecks (by decide) sha512_224_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_224_initImp

/-! ## SHA-512/256 -/

theorem sha512_256_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.X86.sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_finChecks : HmacFin.Checks VG.Proof.Pbkdf2.Md.X86.sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_iterImp : (iterW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.iterSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using VG.Proof.Pbkdf2.Md.X86.Instances.iterSat 192 32 234

theorem sha512_256_finImp : (finW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.finSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using VG.Proof.Pbkdf2.Md.X86.Instances.finSat 192 32 234

theorem sha512_256_iterate : Verified X86.target sha512_256M.iterate (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512_256Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha512_256_iterChecks (by decide) sha512_256_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_256_iterImp

theorem sha512_256_finalize : Verified X86.target sha512_256M.hmacFin (Spec.Hmac.sha512_256I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512_256Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha512_256_finChecks (by decide) sha512_256_finImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_256_finImp

theorem sha512_256_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.X86.sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_initImp : (initW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := VG.Proof.Pbkdf2.Md.X86.Instances.initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using VG.Proof.Pbkdf2.Md.X86.Instances.initSat 192 234

theorem sha512_256_init : Verified X86.target sha512_256M.hmacInit (Spec.Hmac.sha512_256I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW VG.Proof.Pbkdf2.Md.X86.sha512_256Ok VG.Proof.Pbkdf2.Md.X86.Instances.sha512_256_initChecks (by decide) sha512_256_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.X86.Instances.sha512_256_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances

/-! ## Hash functions with a backend for each implementation of their compression function

Their code differs between backends only in the functions it calls, so its
taint checks are evaluated once, on the code without them (`shapeOf`), for
every backend (`Sha256.lean`, `Sha1.lean`). -/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.Impl.Pbkdf2.Md.X86 (Hash)

/-- `H` without the names and code of the functions it calls: the code
between the calls depends on nothing else. -/
def shapeOf (H : Hash) : Hash :=
  ⟨⟨H.st.B, H.st.S, H.st.D, H.st.F, H.st.W, "", .block [], "", .block [], "", .block []⟩, H.N, H.L, H.be, H.so,
    "", .block [], H.out⟩

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.Proof.Pbkdf2.Md.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)

theorem iterChecks_of_shape {H : Hash} (h : Iterate.Checks (VG.Proof.Pbkdf2.Md.X86.shapeOf H)) : Iterate.Checks H :=
  ⟨h.pro, h.load, h.mid, h.tail, h.restore⟩

theorem initChecks_of_shape {H : Hash} (h : HmacInit.Checks (VG.Proof.Pbkdf2.Md.X86.shapeOf H)) : HmacInit.Checks H :=
  ⟨h.pro, h.blocks, h.toOuter, h.restore⟩

theorem finChecks_of_shape {H : Hash} (h : HmacFin.Checks (VG.Proof.Pbkdf2.Md.X86.shapeOf H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.out⟩

end VG.Proof.Pbkdf2.Md.X86.Instances

end
