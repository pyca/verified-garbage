module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Sha512.Stream
public import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86.Lit
public import VerifiedGarbage.Proof.MdStream.X86.Update
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.X86.Update
meta import VerifiedGarbage.Proof.MdStream.X86.Words
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Proof.Sha512.X86.Compress
meta import VerifiedGarbage.Impl.Sha512.X86.Stream
meta import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `Sha512.X86.Stream.Finalize`, which the modules that import this one used -/

section

/-! ### `Sha512.X86.Stream.Update`, which this module and modules that import it used -/

section

/-!
# Streaming SHA-512 on x86 (32-bit): `update`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for the SHA-512 family's instance
(`Proof/Sha512/Md.lean`) with 272 bytes of scratch space, given that its
compression function is verified (`callee`) and that the taint analysis
accepts its code (which it checks together with the compression function's).
`Finalize.lean` adds what the family's length field and digest do.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev params := Impl.Sha512.X86.Stream.params

theorem dims : Dims params 272 := ⟨.inr rfl, by decide, by decide, by decide, by decide⟩

theorem callee : CalleeOk (P := params) md Impl.Sha512.X86.compress :=
  ⟨Compress.compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Sha512.X86.Stream.update Proof.Sha512.updateX86 :=
  MdStream.X86.Update.verified (name := "vg_sha512_compress") dims callee
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Update.τ₀ params 272)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide))

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat params 272

end Update

end VG.Proof.Sha512.X86.Stream

end

end

/-!
# Streaming SHA-512 on x86 (32-bit): `finalize`

The generic `finalize` (`Proof/MdStream/X86/`) for the SHA-512 family, given
what its length field and digest do (`shape`): the length in bits as a 128-bit
big-endian integer, `count >> 61` then `count << 3`, and the words of the hash
value big-endian, each the big-endian bytes of its high half, then of its low
half.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Impl.MdStream.X86 (len64Of out64)
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append)

/-- `count >> 61`, from the halves of `count`. -/
theorem shr61 (hi lo : BitVec 32) : (hi ++ lo) >>> 61 = (0 : BitVec 32) ++ hi >>> 29 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_append]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or,
    ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  have := lo.isLt
  omega_using []

/-- The length field: `count >> 61`, then `8 count`, big-endian. -/
theorem lenOf_eq (hi lo : BitVec 32) :
    md.lenOf (hi ++ lo) = bytes32 true 0 ++ bytes32 true (hi >>> 29) ++
      bytes64 true (BitVec.ofNat 64 (8 * (hi ++ lo).toNat)) := by
  have e := Proof.Sha512.lenOf_split (hi ++ lo)
  rw [shr61] at e
  rw [show md.lenOf (hi ++ lo) = Spec.Sha512.wordBytes ((0 : BitVec 32) ++ hi >>> 29) ++
    Spec.Sha512.wordBytes (BitVec.ofNat 64 (8 * (hi ++ lo).toNat)) from e,
    show Spec.Sha512.wordBytes = bytes64 true from rfl, bytes64_halves]
  rfl

theorem len_ok (s : State) (hfit : (s.gpr .ebx).toNat + (params.N + params.B) ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (params.so + 16)) 4)
    (hhi : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (params.so + 20)) 4)
    (ho : ∀ d, params.N + params.B - params.L ≤ d → d + 4 ≤ params.N + params.B →
      InRegions s.wr (addr (s.gpr .ebx) d) 4) :
    WP isa (.block params.len) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (params.N + params.B - params.L))
        (md.lenOf (s.mem.readW (addr (s.gpr .ebp) (params.so + 20)) 32 ++
          s.mem.readW (addr (s.gpr .ebp) (params.so + 16)) 32)) := by
  have hfit' : (s.gpr .ebx).toNat + 192 ≤ 2 ^ 32 := hfit
  have ho' : ∀ d, 176 ≤ d → d + 4 ≤ 192 → InRegions s.wr (addr (s.gpr .ebx) d) 4 := ho
  show WP isa (.block (Impl.MdStream.X86.loadCount 224 ++ ([.mov .edx (.imm 0), .store (at_ .ebx 176) .edx,
    .mov .edx (.reg .ecx), .shift .shr .edx 29, .bswap .edx, .store (at_ .ebx 180) .edx] ++
    len64Of 184 true))) s fun s' => _ ∧ _ ∧ _ ∧ s'.mem = writeBytes s.mem ((s.gpr .ebx).setWidth 64 +
      BitVec.ofNat 64 176) (md.lenOf (s.mem.readW (addr (s.gpr .ebp) 244) 32 ++
        s.mem.readW (addr (s.gpr .ebp) 240) 32))
  refine loadCount_ok hlo hhi fun s₂ g₂ m₂ rd₂ wr₂ ha hc => ?_
  generalize s.mem.readW (addr (s.gpr .ebp) (224 + 16)) 32 = lo at ha
  generalize s.mem.readW (addr (s.gpr .ebp) (224 + 20)) 32 = hi at hc
  have hb₂ : s₂.gpr .ebx = s.gpr .ebx := g₂ _ (by decide) (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₃ u₃ => wp_store (a := addr (s.gpr .ebx) 176)
    (by show addr (s₃.gpr .ebx) 176 = _; rw [u₃.other _ (by decide), hb₂]) (by rw [u₃.wr, wr₂]; exact ho' 176 (by omega_using []) (by omega_using []))
    fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_shr (by decide) fun s₆ u₆ => wp_bswap fun s₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .edx → s₇.gpr r = s₂.gpr r := fun r h => by
    rw [u₇.other r h, u₆.other r h, u₅.other r h, u₄.gpr, u₃.other r h]
  refine wp_store (a := addr (s.gpr .ebx) 180) (by show addr (s₇.gpr .ebx) 180 = _; rw [g₇ _ (by decide), hb₂])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]; exact ho' 180 (by omega_using []) (by omega_using [])) fun s₈ u₈ => ?_
  have g₈ : ∀ r, r ≠ .edx → s₈.gpr r = s₂.gpr r := fun r h => by rw [u₈.gpr, g₇ r h]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]
  refine (len64Of_ok (d := 184) (be := true) (hi := hi) (lo := lo) (by rw [g₈ _ (by decide), hb₂]; omega_using [hfit'])
    (by rw [g₈ _ (by decide), ha]) (by rw [g₈ _ (by decide), hc])
    (by rw [wr₈, g₈ _ (by decide), hb₂]; exact ho' 184 (by omega_using []) (by omega_using []))
    (by rw [wr₈, g₈ _ (by decide), hb₂]; exact ho' 188 (by omega_using []) (by omega_using []))).mono
    fun s' ⟨g', rd', wr', m'⟩ => ⟨fun r h1 h2 h3 => by rw [g' r h1 h2 h3, g₈ r h3, g₂ r h1 h2],
      by rw [rd', u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂], by rw [wr', wr₈], ?_⟩
  have v₃ : s₃.gpr .edx = bswap 0 := by rw [u₃.gpr]; decide
  have v₇ : s₇.gpr .edx = bswap (hi >>> 29) := by rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), hc]
  have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => writeW32 m a true x
  simp only [ite_true] at w
  have e₀ : addr (s.gpr .ebx) 176 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 176 := addr_eq (by omega_using [hfit'])
  have e₁ : addr (s.gpr .ebx) 180 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 176 +
      BitVec.ofNat 64 (bytes32 true 0).length := by rw [addr_eq (by omega_using [hfit']), bytes32_length, add_ofNat]
  have e₂ : (s₈.gpr .ebx).setWidth 64 + BitVec.ofNat 64 184 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 176 +
      BitVec.ofNat 64 (bytes32 true 0 ++ bytes32 true (hi >>> 29)).length := by
    rw [g₈ _ (by decide), hb₂, List.length_append, bytes32_length, bytes32_length, add_ofNat]
  rw [m', e₂, u₈.mem, v₇, u₇.mem, u₆.mem, u₅.mem, u₄.mem, v₃, u₃.mem, m₂, w, w, e₀, e₁,
    writeBytes_append _ _ _ _ (by simp [bytes32_length]),
    writeBytes_append _ _ _ _ (by simp [bytes32_length, bytes64_length]), lenOf_eq]

theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 32) := by
  have h : md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
    simp [md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes64,
      Spec.Sha512.wordBytes]
  have e : ∀ k, bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) =
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 32) := fun k => by
    rw [Proof.Sha512.Word64.readW64, bytes64_halves, ← add_ofNat]
    rfl
  rw [h]
  exact congrArg (fun f => (List.range 8).flatMap f) (funext e)

theorem shape : Shape (P := params) md where
  len s hfit hlo hhi ho := len_ok s hfit hlo hhi ho
  out _ hbx hax hin hout hd := by
    refine (out64_ok (n := 8) (by decide) hbx hax hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ =>
      ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

namespace Finalize

theorem finalize_verified : Verified X86.target Impl.Sha512.X86.Stream.finalize Proof.Sha512.finalizeX86 :=
  MdStream.X86.Finalize.verified_ro (name := "vg_sha512_compress") dims shape callee
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Finalize.τ₀ params 272)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide))

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86.Finalize.satR params 272

end Finalize

end VG.Proof.Sha512.X86.Stream

end

end

/-!
# Streaming SHA-512 on x86 (32-bit): `init`

One proof for every initial hash value `iv`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Impl.Sha512.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha512.Word64 (lo hi)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_store wp_movm contains_addr)
open VG.Spec.Sha512 (HashValue stateAt)

/-- After the first `n` words of `iv`, with `eax` = `state`. -/
structure IInv (iv : HashValue) (s₀ : State) (st : BitVec 32) (n : Nat) (s : State) : Prop where
  eax : s.gpr .eax = st
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨st.setWidth 64, 192⟩] s₀.mem s.mem
  words : ∀ k < n, rd64 s.mem st (8 * k) = iv[k]!

theorem initW_ok (iv : HashValue) {s₀ : State} {st : BitVec 32} (hfit : st.toNat + 192 ≤ 2 ^ 32)
    (hR : ⟨st.setWidth 64, 192⟩ ∈ s₀.wr) {n : Nat} (hn : n < 8) {s : State} (h : IInv iv s₀ st n s) :
    WP isa (.block (initW iv n)) s (IInv iv s₀ st (n + 1)) := by
  have c : ∀ o, o + 4 ≤ 192 → (⟨st.setWidth 64, 192⟩ : Region).Contains (addr st o) (32 / 8) :=
    fun o ho => contains_addr ho (by decide) hfit
  have o : ∀ o, o + 4 ≤ 192 → InRegions s.wr (addr st o) 4 :=
    fun o ho => ⟨_, by rw [h.wr]; exact hR, c o ho⟩
  simp only [initW]
  refine wp_movi fun s₁ u₁ => wp_store (a := addr st (8 * n))
    (by rw [ea_of (u₁.other _ (by decide) |>.trans h.eax)]) (by rw [u₁.wr]; exact o _ (by omega_using [hn]))
    fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  refine wp_store (a := addr st (8 * n + 4))
    (by rw [ea_of ((u₃.other _ (by decide)).trans (by rw [u₂.gpr, u₁.other _ (by decide), h.eax]))])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o _ (by omega_using [hn])) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = write64 s.mem st (8 * n) iv[n]! := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
    rfl
  refine ⟨?_, fun r h₁ h₂ => ?_, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_, fun k hk => ?_⟩
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.eax]
  · rw [u₄.gpr, u₃.other _ h₂, u₂.gpr, u₁.other _ h₂, h.gpr r h₁ h₂]
  · rw [hm]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (c _ (by omega_using [hn]))).writeW
      (List.mem_singleton_self _) _ (c _ (by omega_using [hn]))
  · rw [hm]
    by_cases hkn : k = n
    · subst hkn; exact rd64_write64_self _ _ (by omega_using [hfit, hn])
    · rw [rd64_write64_ne _ _ (by omega_using [hfit, hn]) (by omega_using [hfit, hn, hk]) (by omega_using [hkn])]
      exact h.words k (by omega_using [hk, hkn])

theorem init_all (iv : HashValue) {s₀ : State} {st : BitVec 32} (hfit : st.toNat + 192 ≤ 2 ^ 32)
    (hR : ⟨st.setWidth 64, 192⟩ ∈ s₀.wr) {s : State} (h : IInv iv s₀ st 0 s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (initW iv))) s (IInv iv s₀ st n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact initW_ok iv hfit hR (by omega_using [hn]) h

theorem init_correct (iv : HashValue) {s₀ : State} (hp : (Proof.Sha512.initX86 iv).pre s₀) :
    WP isa (init iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha512.initX86 iv).post s₀ s' := by
  obtain ⟨hrd, hwr, -, hret, hfit, -⟩ := hp
  let st := arg s₀ 0
  try rewrite [show arg s₀ 0 = st from rfl] at *
  have hst : st = arg s₀ 0 := rfl
  have hR : ⟨st.setWidth 64, 192⟩ ∈ s₀.wr := by simp [hwr]
  refine wp_movm (a := addr (s₀.gpr .esp) 4) rfl
    ⟨⟨argAddr s₀ 0, 4⟩, by simp [hrd], Region.contains_self _ _⟩ fun s₁ u₁ => ?_
  refine WP.mono (init_all iv hfit hR ⟨u₁.gpr, fun r h _ => u₁.other r h, u₁.rd, u₁.wr,
    by rw [u₁.mem]; exact Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩ 8 (Nat.le_refl _))
    fun s h => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · refine h.gpr r ?_ ?_ <;>
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · exact h.frame.readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · refine Proof.Sha512.Stream.repr_nil (stateAt_ext (by rw [← hst]; omega_using [hfit]) fun k hk => ?_)
    rw [h.words k hk, getElem!_pos iv k hk]

/-- Memory holding the argument `0x1000` at `0x4004`. -/
def initSatMem : Mem := fun a => if a = 0x4005 then 0x10 else 0

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initSatMem
  rd := [⟨0x4004, 4⟩]
  wr := [⟨0x1000, 192⟩]

theorem initSat_pre (iv : HashValue) : (Proof.Sha512.initX86 iv).pre initSat := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have e : argAddr initSat 0 = 0x4004 := by decide
  simp only [Proof.Sha512.initX86, a0, e]
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The initial taint: the argument is public, and the word holding `state`
is the base address of the writable region. -/
def initτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [192], argLen := 8, argBases := [(4, 0)] }

theorem init_agree₀ (iv : HashValue) {s₁ s₂ : State} (h₁ : (Proof.Sha512.initX86 iv).pre s₁)
    (h₂ : (Proof.Sha512.initX86 iv).pre s₂) (hpub : (Proof.Sha512.initX86 iv).pub s₁ s₂) :
    VG.X86.Taint.Agree initτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  have wf : ∀ s, (Proof.Sha512.initX86 iv).pre s → VG.X86.Taint.Wf initτ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, hr, hfit, hsp⟩ := hs
    refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, initτ₀], by simp [hw], ?_⟩,
      fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
      fun _ => ⟨hsp, ?_⟩, ?_⟩
    · simp only [hw, List.mem_singleton]
      rintro r rfl; simp only [BitVec.toNat_setWidth]; omega_using [hfit]
    · simp only [hw, List.mem_singleton]
      rintro r rfl
      exact VG.X86.Taint.frame_disjoint (n := 4) (by omega_using [hsp]) hr hd
    · intro p hp'
      simp only [initτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'; refine ⟨by decide, ?_⟩
      simp [VG.X86.Taint.region, hw, addr, arg, argAddr]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf _ h₁, wf _ h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [initτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1, a0]
  · simp only [initτ₀] at hk
    rw [show VG.X86.Taint.depth initτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq h₁.2.2.2.2.2 h4 hk, VG.X86.Taint.argByte_eq h₂.2.2.2.2.2 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using [])),
      show (k - 4) / 4 = 0 by omega_using [hk]]
    exact congrArg _ a0

/-- The hint for `init 0`, which is also one for `init iv`. -/
abbrev initHint : VG.Taint.Hint taint.T := VG.Taint.hintOf taint initτ₀ (init 0)

/-- The taint check never looks at an immediate, so the kernel evaluates it on
`init iv` for any `iv`. -/
theorem init_check (iv : HashValue) : (taint.check initτ₀ (init iv) initHint).isSome = true := by
  kernel_rfl

theorem init_verified (iv : HashValue) :
    Verified X86.target (init iv) (Proof.Sha512.initX86 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, initSat_pre iv⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct iv hs
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) initτ₀ (fun _ _ h₁ h₂ hp => init_agree₀ iv h₁ h₂ hp)
      (init_check iv)

end VG.Proof.Sha512.X86.Stream
