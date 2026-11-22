module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Returning without secret residue, for code that wipes its own frame (x86, 32-bit)

`withStackScratchWiped bytes (slots sig) words c` (`Impl/StackScratch/X86.lean`)
runs `c` in a frame of `bytes` bytes, and zeroes its buffer before it
releases the frame. When `c` has no frame and calls nothing, it writes no
stack below the frame, and the frame holds, on release:

* its first word, which nothing writes: what the stack held there on entry;
* the copies of the arguments (`setArgs`), which the code reads, and the
  buffer's address, a function of `esp`;
* the buffer, zeroed if the wipe covers all of it (`4 * words = n * e.size`);
* the rest, which nothing writes.

`c` writes only what its contract with the buffer lets it (`narrow`,
`Exec.regions`): its buffers and the buffer, and not the copies of its
arguments if that contract does not let it write them (`wa = false`). So
two runs that agree on the arguments (which `hargs` gives of two runs that
agree on what is public) and on everything outside the buffers end, before
the frame's release, agreeing on the frame (`wiped_agree`). The release
loses its bytes as the two runs' unknowns say, which are the same in both
(`Exec.path`, from the same trace), so the function returns without secret
residue followed only by the clearing of the registers, `scrub rb`, which
wipes no stack (`verifiedScrubbedWiped`).

This is `PPC64LE.Scrub.verifiedScrubbedWiped` on x86. There a frame's
region leaves out its header, which code in it cannot write; on x86 the
frame's region is all of it, and the contract of the code in it says what
it writes. Code that has a frame or a call inside the wiped one, or whose
contract may write its argument slots, stays on `scrubAll`.
-/

@[expose] public section

namespace VG.X86.Scrub

open VG.Impl.Scrub.X86 VG.Impl.StackScratch.X86

/-- Code that calls nothing calls no function indirectly. -/
theorem inames_of_noCalls : ∀ {c : Prog isa}, c.noCalls = true → inames c = []
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [inames, inames_of_noCalls h.1, inames_of_noCalls h.2, List.append_nil]
  | .ite _ t e, h => by
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [inames, inames_of_noCalls h.1, inames_of_noCalls h.2, List.append_nil]
  | .loop b _, h => inames_of_noCalls (c := b) h
  | .call .., h => by simp [Code.noCalls] at h
  | .frame .., h => by simp [Code.noCalls] at h
  | .icall .., h => by simp [Code.noCalls] at h

/-- A store of `w / 8` zero bytes at offset `hi` from `q`, after the bytes
from `lo` to `hi` zeroed, is the bytes from `lo` to `hi + w / 8` zeroed. -/
theorem zeroOn_writeW_top (q : Addr) {lo hi w : Nat} (hl : lo ≤ hi) (hh : hi + w / 8 ≤ 2 ^ 64) (m : Mem) :
    (zeroOn q lo hi m).writeW (q + BitVec.ofNat 64 hi) (0 : BitVec w) = zeroOn q lo (hi + w / 8) m := by
  funext x
  have e := Offset.lt_iff x q (d := hi) (n := w / 8) hh
  simp only [zeroOn, Mem.writeW, Mem.write]
  generalize (x - (q + BitVec.ofNat 64 hi)).toNat = r at e ⊢
  generalize (x - q).toNat = d at e ⊢
  repeat' split
  all_goals first | (exfalso; omega) | rfl | simp

/-- Zeroing changes memory only in the bytes zeroed. -/
theorem zeroOn_frame (q : Addr) {lo hi : Nat} (h : hi ≤ 2 ^ 64) (m : Mem) :
    Frame [⟨q + BitVec.ofNat 64 lo, hi - lo⟩] m (zeroOn q lo hi m) := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  by_cases hlo : lo ≤ hi
  · have e := Offset.lt_iff x q (d := lo) (n := hi - lo) (by omega_using [hlo, h])
    simp only [zeroOn]
    split
    · next h' => exfalso; exact hc (by have := e.mpr ⟨h'.1, by omega_using [h'.2, hlo]⟩; omega_using [this])
    · rfl
  · simp only [zeroOn]
    split
    · next h' => exfalso; omega_using [h'.1, h'.2, hlo]
    · rfl

/-- `wipeStores off w` from `u`, whose `ecx` is zero and whose `esp` is `E`,
which may write the `L` bytes at offset `b` from `E`, from `off` to
`off + 4 W` among them: it zeroes the bytes at offsets `off` to `off + 4 w`
from `E`. -/
theorem wipeStores_zero (E : BitVec 32) (off W b L : Nat) (hb : b ≤ off) (hL : off + 4 * W ≤ b + L)
    (hq : E.toNat + b + L ≤ 2 ^ 32) (u : State)
    (h0 : u.gpr .ecx = 0) (h1 : u.gpr .esp = E)
    (hw : (⟨E.setWidth 64 + BitVec.ofNat 64 b, L⟩ : Region) ∈ u.wr) :
    ∀ w, w ≤ W → execBlock isa (wipeStores off w) u =
      some ({ u with mem := zeroOn (E.setWidth 64) off (off + 4 * w) u.mem }, wipeTrace4 E off w)
  | 0, _ => by
    simp only [wipeStores, List.range_zero, List.map_nil, execBlock, Nat.mul_zero, Nat.add_zero, zeroOn_self,
      wipeTrace4]
  | w + 1, hk => by
    have hlt : E.toNat + (off + 4 * w) < 2 ^ 32 := by omega_using [hk, hq, hL]
    have ha : (E + BitVec.ofNat 32 (off + 4 * w)).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 (off + 4 * w) :=
      addr_eq hlt
    rw [wipeStores_succ, execBlock_append, wipeStores_zero E off W b L hb hL hq u h0 h1 hw w (by omega_using [hk])]
    have hin : InRegions ({ u with mem := zeroOn (E.setWidth 64) off (off + 4 * w) u.mem } : State).wr
        ((({ u with mem := zeroOn (E.setWidth 64) off (off + 4 * w) u.mem } : State).gpr .esp +
          BitVec.ofNat 32 (off + 4 * w)).setWidth 64) 4 :=
      ⟨_, hw, by
        show (⟨E.setWidth 64 + BitVec.ofNat 64 b, L⟩ : Region).Contains
          ((u.gpr .esp + BitVec.ofNat 32 (off + 4 * w)).setWidth 64) 4
        rw [h1, ha]
        exact Offset.contains _ (by omega_using [hb]) (by omega_using [hk, hL]) (by omega_using [hk, hq])⟩
    simp only [Option.bind_some, execBlock, isa, exec, State.store32, State.ea, hin, ↓reduceIte,
      Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · show { u with mem := ((zeroOn (E.setWidth 64) off (off + 4 * w) u.mem).writeW
          ((u.gpr .esp + BitVec.ofNat 32 (off + 4 * w)).setWidth 64) (u.gpr .ecx)) } = _
      rw [h1, h0, ha, zeroOn_writeW_top _ (by omega_using []) (by omega_using [hk, hq, hL]),
        show off + 4 * w + 32 / 8 = off + 4 * (w + 1) by omega_using []]
    · show wipeTrace4 E off w ++ [.addr ((u.gpr .esp + BitVec.ofNat 32 (off + 4 * w)).setWidth 64)] = _
      rw [h1]
      simp only [wipeTrace4, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- `wipeStores16 off w` from `u`, whose `xmm0` is zero and whose `esp` is
`E`, which may write the `L` bytes at offset `b` from `E`, from `off` to
`off + 16 W` among them: it zeroes the bytes at offsets `off` to
`off + 16 w` from `E`. -/
theorem wipeStores16_zero (E : BitVec 32) (off W b L : Nat) (hb : b ≤ off) (hL : off + 16 * W ≤ b + L)
    (hq : E.toNat + b + L ≤ 2 ^ 32) (u : State)
    (h0 : u.xmm .xmm0 = 0) (h1 : u.gpr .esp = E)
    (hw : (⟨E.setWidth 64 + BitVec.ofNat 64 b, L⟩ : Region) ∈ u.wr) :
    ∀ w, w ≤ W → execBlock isa (wipeStores16 off w) u =
      some ({ u with mem := zeroOn (E.setWidth 64) off (off + 16 * w) u.mem }, wipeTrace16 E off w)
  | 0, _ => by
    simp only [wipeStores16, List.range_zero, List.map_nil, execBlock, Nat.mul_zero, Nat.add_zero, zeroOn_self,
      wipeTrace16]
  | w + 1, hk => by
    have hlt : E.toNat + (off + 16 * w) < 2 ^ 32 := by omega_using [hk, hq, hL]
    have ha : (E + BitVec.ofNat 32 (off + 16 * w)).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 (off + 16 * w) :=
      addr_eq hlt
    rw [wipeStores16_succ, execBlock_append, wipeStores16_zero E off W b L hb hL hq u h0 h1 hw w (by omega_using [hk])]
    have hin : InRegions ({ u with mem := zeroOn (E.setWidth 64) off (off + 16 * w) u.mem } : State).wr
        ((({ u with mem := zeroOn (E.setWidth 64) off (off + 16 * w) u.mem } : State).gpr .esp +
          BitVec.ofNat 32 (off + 16 * w)).setWidth 64) 16 :=
      ⟨_, hw, by
        show (⟨E.setWidth 64 + BitVec.ofNat 64 b, L⟩ : Region).Contains
          ((u.gpr .esp + BitVec.ofNat 32 (off + 16 * w)).setWidth 64) 16
        rw [h1, ha]
        exact Offset.contains _ (by omega_using [hb]) (by omega_using [hk, hL]) (by omega_using [hk, hq])⟩
    simp only [Option.bind_some, execBlock, isa, exec, State.store128, State.ea, hin, ↓reduceIte,
      Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · show { u with mem := ((zeroOn (E.setWidth 64) off (off + 16 * w) u.mem).writeW
          ((u.gpr .esp + BitVec.ofNat 32 (off + 16 * w)).setWidth 64) (u.xmm .xmm0)) } = _
      rw [h1, h0, ha, zeroOn_writeW_top _ (by omega_using []) (by omega_using [hk, hq, hL]),
        show off + 16 * w + 128 / 8 = off + 16 * (w + 1) by omega_using []]
    · show wipeTrace16 E off w ++ [.addr ((u.gpr .esp + BitVec.ofNat 32 (off + 16 * w)).setWidth 64)] = _
      rw [h1]
      simp only [wipeTrace16, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- `wipe off words` from `u`, whose `esp` is `E`, which may write the
`4 words` bytes at offset `off` from `E`: it sets `xmm0` and `ecx` to zero
and zeroes them. -/
theorem wipe_zero (E : BitVec 32) (off words : Nat) (hq : E.toNat + off + 4 * words ≤ 2 ^ 32)
    (u : State) (h1 : u.gpr .esp = E) (hw : (⟨E.setWidth 64 + BitVec.ofNat 64 off, 4 * words⟩ : Region) ∈ u.wr) :
    execBlock isa (Impl.StackScratch.X86.wipe off words) u =
      some ({ wipeRegs u with mem := zeroOn (E.setWidth 64) off (off + 4 * words) u.mem },
        wipeTrace E off words) := by
  have hsp : (wipeRegs u).gpr .esp = E := (wipeRegs_gpr (by decide)).trans h1
  have he₁ := wipeStores16_zero E off (words / 4) off (4 * words) (Nat.le_refl _) (by omega_using [])
    (by omega_using [hq]) (wipeRegs u) (wipeRegs_xmm0 u) hsp (by rw [wipeRegs_wr]; exact hw) (words / 4)
    (Nat.le_refl _)
  have he₂ := wipeStores_zero E (off + 16 * (words / 4)) (words % 4) off (4 * words) (by omega_using [])
    (by omega_using []) (by omega_using [hq])
    { wipeRegs u with mem := zeroOn (E.setWidth 64) off (off + 16 * (words / 4)) (wipeRegs u).mem }
    (wipeRegs_ecx u) hsp (by rw [show ({ wipeRegs u with mem := _ } : State).wr = u.wr from rfl]; exact hw)
    (words % 4) (Nat.le_refl _)
  have e₀ : execBlock isa [.xop (.bin .pxor .xmm0 .xmm0), .mov .ecx (.imm 0)] u = some (wipeRegs u, []) := by
    simp [execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, wipeRegs, XOp.exec, XBinOp.eval,
      BitVec.xor_self]
  rw [Impl.StackScratch.X86.wipe, show (.xop (.bin .pxor .xmm0 .xmm0) :: .mov .ecx (.imm 0) ::
      (wipeStores16 off (words / 4) ++ wipeStores (off + 16 * (words / 4)) (words % 4)) : List Instr) =
      [.xop (.bin .pxor .xmm0 .xmm0), .mov .ecx (.imm 0)] ++
        (wipeStores16 off (words / 4) ++ wipeStores (off + 16 * (words / 4)) (words % 4)) from rfl,
    execBlock_append, e₀, Option.bind_some, execBlock_append, he₁, Option.bind_some, he₂]
  simp only [Option.map_some, List.nil_append, wipeTrace, wipeRegs_mem]
  rw [zeroOn_zeroOn _ (by omega_using []) (by omega_using []),
    show off + 16 * (words / 4) + 4 * (words % 4) = off + 4 * words by omega_using []]

/-- A byte of a released frame depends only on what it held, where the
frame is and the unknowns. -/
theorem lose_congr {m₁ m₂ : Mem} {x : Addr} (h : m₁ x = m₂ x) (a : Addr) (k : Nat) (U : Nat → BitVec 32) :
    lose m₁ a k U x = lose m₂ a k U x := by
  simp only [lose, h]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {bytes words : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What `narrow` holds outside the buffers: two states that agree there, on
the stack pointer and on the arguments, give `narrow` states that agree
there. Outside the copies of the arguments and the buffer's address it is
the state's memory; in them, the arguments and the stack pointer's. -/
theorem narrow_mem_agree (hb : 8 + 4 * slots sig + n * e.size ≤ bytes) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post false (0 + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post false (0 + bytes) leak).pre s₂)
    (hsp : s₁.gpr .esp = s₂.gpr .esp) (hargs : ∀ j < slots sig, arg s₁ j = arg s₂ j)
    {x : Addr} (hm : s₁.mem x = s₂.mem x) :
    (narrow sig e n bytes false s₁).mem x = (narrow sig e n bytes false s₂).mem x := by
  obtain ⟨-, -, -, hg₁, hf₁, hv₁, hl₁⟩ := argsState_run (n := n) (e := e) h₁ hb
  obtain ⟨-, -, -, hg₂, hf₂, hv₂, hl₂⟩ := argsState_run (n := n) (e := e) h₂ hb
  have hst := ((pre_stackL.mp h₁).1)
  rw [narrow_mem, narrow_mem]
  -- The frame's base, in both runs.
  generalize hE : s₁.gpr .esp - BitVec.ofNat 32 bytes = E at hl₁
  have hE₂ : s₂.gpr .esp - BitVec.ofNat 32 bytes = E := by rw [← hsp]; exact hE
  rw [hE₂] at hl₂
  have hEn : E.toNat = (s₁.gpr .esp).toNat - bytes := by rw [← hE]; exact sub_toNat (by omega_using [hst])
  have hu₁ : ((allocState bytes s₁).gpr .esp) = E := by rw [allocState_esp, hE]
  have hu₂ : ((allocState bytes s₂).gpr .esp) = E := by rw [allocState_esp, hE₂]
  rw [hu₁] at hf₁
  rw [hu₂] at hf₂
  by_cases hH : (⟨E.setWidth 64 + 4, 4 * (slots sig + 1)⟩ : Region).Contains x 1
  · -- A byte of the copies: byte `i` of slot `j`.
    simp only [Region.Contains] at hH
    generalize hd : (x - (E.setWidth 64 + 4)).toNat = d at hH
    have hx : x = E.setWidth 64 + BitVec.ofNat 64 (4 + 4 * (d / 4)) + BitVec.ofNat 64 (d % 4) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4 + 4 * (d / 4) + d % 4 = 4 + d by omega_using [],
        BitVec.ofNat_add, ← BitVec.add_assoc, ← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      show x = E.setWidth 64 + 4 + (x - (E.setWidth 64 + 4))
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    have hA : ∀ (u : State), u.gpr .esp = E → argAddr u (d / 4) = E.setWidth 64 + BitVec.ofNat 64 (4 + 4 * (d / 4)) :=
      fun u hu => by
        simp only [argAddr, hu]
        exact addr_eq (x := E) (k := 4 + 4 * (d / 4)) (by omega_using [hEn, hst, hb, hH])
    have hesp₁ : (setArgsState bytes (slots sig) (allocState bytes s₁)).gpr .esp = E := by
      rw [hg₁ _ (by decide), hu₁]
    have hesp₂ : (setArgsState bytes (slots sig) (allocState bytes s₂)).gpr .esp = E := by
      rw [hg₂ _ (by decide), hu₂]
    have hw : arg (setArgsState bytes (slots sig) (allocState bytes s₁)) (d / 4) =
        arg (setArgsState bytes (slots sig) (allocState bytes s₂)) (d / 4) := by
      by_cases hj : d / 4 < slots sig
      · rw [hv₁ _ hj, hv₂ _ hj, hargs _ hj]
      · obtain e' : d / 4 = slots sig := by omega_using [hj, hH]
        rw [e', hl₁, hl₂]
    have k₁ : (setArgsState bytes (slots sig) (allocState bytes s₁)).mem.readW
        (E.setWidth 64 + BitVec.ofNat 64 (4 + 4 * (d / 4))) 32 =
        arg (setArgsState bytes (slots sig) (allocState bytes s₁)) (d / 4) := by
      simp only [arg, hA _ hesp₁]
    have k₂ : (setArgsState bytes (slots sig) (allocState bytes s₂)).mem.readW
        (E.setWidth 64 + BitVec.ofNat 64 (4 + 4 * (d / 4))) 32 =
        arg (setArgsState bytes (slots sig) (allocState bytes s₂)) (d / 4) := by
      simp only [arg, hA _ hesp₂]
    rw [hx, Mem.readW_byte (setArgsState bytes (slots sig) (allocState bytes s₁)).mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte (setArgsState bytes (slots sig) (allocState bytes s₂)).mem _ (Nat.mod_lt _ (by decide)), k₁, k₂, hw]
  · have hn : ∀ r ∈ [(⟨E.setWidth 64 + 4, 4 * (slots sig + 1)⟩ : Region)], ¬ r.Contains x 1 := by
      intro r hr; rw [List.mem_singleton.mp hr]; exact hH
    rw [hf₁ x hn, hf₂ x hn, hm]


/-- The frame's base, `esp - bytes`, as a 64-bit address. -/
theorem frameBase_eq {s : State} (h : bytes ≤ (s.gpr .esp).toNat) :
    (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes :=
  Taint.sub_setWidth h

/-- A run of `withStackScratchWiped` from `s`: `setArgs`, the code's run from
`narrow s`, the wipe, which zeroes the buffer, and the frame's release. -/
theorem wiped_run {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post false 0 leak))
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hnsp : NoSp c) (hd : stackUse c ≤ 0) (hw : 4 * words = n * e.size)
    (hpreL : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post false (0 + bytes) leak).pre s) :
    ∃ t s₃, Exec isa c (narrow sig e n bytes false s) t s₃ ∧
      Exec isa (withStackScratchWiped bytes (slots sig) words c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++
          (t ++ wipeTrace (s.gpr .esp - BitVec.ofNat 32 bytes) (8 + 4 * slots sig) words))
        (popState bytes s { wipeRegs s₃ with
          mem := zeroOn ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64) (8 + 4 * slots sig)
            (8 + 4 * slots sig + 4 * words) s₃.mem }) := by
  have hst := (pre_stackL.mp hs).1.1
  obtain ⟨t, s₃, he, ha, -⟩ := h.1 _ (narrow_pre hb.1 hpreL hs)
  obtain ⟨hesp, -, -, -⟩ := narrow_facts (nm := "") (e := e) (n := n) hb.1 hs
  generalize hE : s.gpr .esp - BitVec.ofNat 32 bytes = E at hesp ⊢
  have hEn : E.toNat = (s.gpr .esp).toNat - bytes := by rw [← hE]; exact sub_toNat (by omega_using [hst])
  have hesp₃ : s₃.gpr .esp = E := (ha.1 .esp (by simp [calleeSaved])).trans hesp
  have hwr₃ : s₃.wr = (narrow sig e n bytes false s).wr := (Exec.rdwr he).2
  have hoff : (E + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64 =
      E.setWidth 64 + BitVec.ofNat 64 (8 + 4 * slots sig) :=
    addr_eq (by have := (s.gpr .esp).isLt; omega_using [hEn, hst, hb, this])
  have hmem : (⟨E.setWidth 64 + BitVec.ofNat 64 (8 + 4 * slots sig), 4 * words⟩ : Region) ∈ s₃.wr := by
    rw [hwr₃, ← hoff, hw, ← hE]
    simp [narrow, oldRegions]
  have hblk := wipe_zero E (8 + 4 * slots sig) words
    (by have := (s.gpr .esp).isLt; omega_using [hEn, hst, hb, hw, this]) s₃ hesp₃ hmem
  have he' := Exec.seq he (Exec.block hblk)
  have hnsp' : NoSp (.seq c (.block (Impl.StackScratch.X86.wipe (8 + 4 * slots sig) words)) : Prog isa) :=
    fun i hi => by
      simp only [instrs, List.mem_append] at hi
      rcases hi with hi | hi
      · exact hnsp i hi
      · exact wipe_noSp _ _ i hi
  have hd' : stackUse (.seq c (.block (Impl.StackScratch.X86.wipe (8 + 4 * slots sig) words)) : Prog isa) ≤ 0 := by
    simp only [stackUse]; omega_using [hd]
  have ha' : abiPreserved (narrow sig e n bytes false s) { wipeRegs s₃ with
      mem := zeroOn (E.setWidth 64) (8 + 4 * slots sig) (8 + 4 * slots sig + 4 * words) s₃.mem } := by
    refine ⟨fun q hq => ?_, ?_⟩
    · have hq' : q ≠ .ecx := by rintro rfl; simp [calleeSaved] at hq
      show (wipeRegs s₃).gpr q = _
      rw [wipeRegs_gpr hq']
      exact ha.1 q hq
    · show (zeroOn _ _ _ s₃.mem).readW _ 32 = _
      rw [hesp]
      have hf := zeroOn_frame (E.setWidth 64) (lo := 8 + 4 * slots sig) (hi := 8 + 4 * slots sig + 4 * words)
        (by omega_using [hb, hw]) s₃.mem
      rw [hf.readW (r := ⟨E.setWidth 64, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hb, hw]))
        (by decide)]
      have h2 := ha.2
      rwa [hesp] at h2
  have hex := withStackScratch_run (stack := 0) hb hnsp' hd' hs he' ha'
  refine ⟨t, s₃, he, ?_⟩
  rw [← hE] at hex ⊢
  exact hex.1

/-- Every argument of `sig` is of 32 bits and public: two runs that agree on
what is public pass the same arguments, which the frame's copies of them
hold. -/
def argsPub (sig : Sig) : Bool :=
  (widths sig).all (· == 32) && (sig.params.flatMap (·.2.pubs)).all id

theorem sum_div32 : ∀ ws : List Nat, ws.all (· == 32) = true → (ws.map (· / 32)).sum = ws.length
  | [], _ => rfl
  | w :: ws, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, List.sum_cons, h.1, List.length_cons, sum_div32 ws h.2]
    omega_using []

theorem argVals_getD (s : State) : ∀ (ws : List Nat) (i₀ j : Nat), ws.all (· == 32) = true → j < ws.length →
    ((ws.zip (argSlots ws i₀)).map fun (w, i) => argVal s w i).getD j 0 = (arg s (i₀ + j)).setWidth 64
  | [], _, _, _, h => absurd h (by simp)
  | w :: ws, i₀, 0, hall, _ => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
    simp [argSlots, hall.1, argVal]
  | w :: ws, i₀, j + 1, hall, hj => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
    simp only [argSlots, hall.1, List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
    rw [argVals_getD s ws (i₀ + 32 / 32) j hall.2 (by simpa using hj)]
    congr 2; omega_using []

/-- Two runs that agree on what is public pass the same arguments, if every
one is of 32 bits and public. -/
theorem args_of_pub {wa : Bool} {stack : Nat} (hpub : argsPub sig = true) (hl : Sig.noLists sig.params = true) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa stack leak).pub s₁ s₂) : ∀ j < slots sig, arg s₁ j = arg s₂ j := by
  intro j hj
  simp only [argsPub, Bool.and_eq_true] at hpub
  obtain ⟨hw, hpb⟩ := hpub
  have lw : (widths sig).length = (sig.params.flatMap fun p => p.2.words abi.ptrBits).length := by
    rw [widths, List.length_map]; rfl
  have hj' : j < (widths sig).length := by rw [← sum_div32 _ hw]; exact hj
  have hpj : (sig.params.flatMap (·.2.pubs)).getD j false = true := by
    have hlen : j < (sig.params.flatMap (·.2.pubs)).length := by
      rw [Sig.pubs_length sig.params abi.ptrBits, ← lw]; exact hj'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    exact List.all_eq_true.mp hpb _ (List.getElem_mem hlen)
  have hwj : (widths sig).getD j 64 = 32 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    exact beq_iff_eq.mp (List.all_eq_true.mp hw _ (List.getElem_mem hj'))
  have h := ((pubL_stack (pre := pre) (post := post) (wa := wa) (stack := stack) (leak := leak) hl).mp hp).2 j hpj
  rw [hwj] at h
  simp only [stackArgs] at h
  rw [argVals_getD s₁ _ 0 j hw hj', argVals_getD s₂ _ 0 j hw hj', Nat.zero_add,
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_eq, BitVec.setWidth_eq] at h
  exact h

/-- What `verifiedScrubbedWiped` needs of the code `c` in the frame: it calls
nothing and has no frame (so it writes no stack below the frame), never
writes `esp`, and the function's code has no MMX instruction. One Boolean,
which the call site proves by `lit_decide`. -/
noncomputable def wipedSide (c : Prog isa) (bytes n words : Nat) : Bool :=
  c.noCalls && stackUse c == 0 && c.allInstrs (fun i => !Taint.clobbers i .esp) &&
    (withStackScratchWiped bytes n words c).allInstrs (fun i => !i.isMmx)

/-- `scrub rb` of code that wipes its own frame (`withStackScratchWiped`,
with a wipe of all of its buffer), whose code in the frame `c` calls
nothing, has no frame and may not write its argument slots (its contract
with the buffer has `wa = false`), meets the function's contract in
constant time and returns without secret residue, if every argument is of
32 bits and public (`argsPub`): `scrub rb` clears the registers alone and
wipes no stack.

`PPC64LE.Scrub.verifiedScrubbedWiped` needs less: there the frame's region
leaves out its header, so code in the frame cannot write it. On x86 the
frame's header (its first word, the copies of the arguments and the
buffer's address) is in the frame's region and is not wiped, so its bytes
must agree in two runs: the code in the frame must not write it (`wa =
false`, which `h` states), nor call or push below the frame (`wipedSide`),
and the copies of the arguments must be public (`argsPub`). AArch64 has no
such form: its code that wipes its own frame still zeroes the stack again
in its cleanup. -/
theorem verifiedScrubbedWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post false 0 leak))
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hw : 4 * words = n * e.size) (hs : wipedSide c bytes (slots sig) words = true)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post false (0 + bytes)).pre s)
    {rb : Nat} (erb : rb = sig.retBits abi.ptrBits)
    (hl : Sig.noLists sig.params = true := by decide)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) (hpub : argsPub sig = true := by decide) :
    VerifiedScrubbed target (scrub rb (withStackScratchWiped bytes (slots sig) words c))
      (sig.contract abi pre post false (0 + bytes) leak) rb := by
  simp only [wipedSide, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨hn, hd0⟩, hsp⟩, hm⟩ := hs
  have hd : stackUse c ≤ 0 := by omega_using [hd0]
  have hnsp : NoSp c := fun i hi => by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    simpa using hsp i hi
  have hpreL : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂ :=
    fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb
  have hA : ScrubAbi abi := ScrubAbi.plain
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [erb, hA.ptrBits]; exact retBits_cases sig
  have hv : Verified target (withStackScratchWiped bytes (slots sig) words c)
      (sig.contract abi pre post false (0 + bytes) leak) :=
    Verified.stackScratchWiped h hb hsp hd (by omega_using [hw]) hpre hpost hpostOut hsat hl hleak
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩, ?_⟩
  · obtain ⟨t, u, he, habi, hq⟩ := hv.1 s hs
    obtain ⟨u', hb', ok⟩ := tail_run hrb u
    refine ⟨t ++ [], u', .seq he (.block hb'), ⟨fun r hr => ?_, by rw [ok.mem]; exact habi.2⟩,
      contract_post_scrub hA hq ok.mem (erb ▸ ok.lo)⟩
    obtain ⟨h0, h1, h2⟩ := saved_ne hr
    rw [ok.gpr r h0 h1 h2]; exact habi.1 r hr
  · obtain ⟨w₁, a₁, -⟩ := exec_scrub hrb e₁
    obtain ⟨w₂, a₂, -⟩ := exec_scrub hrb e₂
    exact hv.2.1 s₁ s₂ t₁ t₂ w₁ w₂ p₁ p₂ hp a₁ a₂
  · intro s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp ho hu e₁ e₂
    -- Each run keeps what the calling convention preserves.
    have keep : ∀ {s u : State} {t : List Leak}, (sig.contract abi pre post false (0 + bytes) leak).pre s →
        Exec isa (scrub rb (withStackScratchWiped bytes (slots sig) words c)) s t u →
        ∃ w, Exec isa (withStackScratchWiped bytes (slots sig) words c) s t w ∧ Ends rb s u ∧
          u.mem = w.mem := by
      intro s u t hs h
      obtain ⟨w, a, b⟩ := exec_scrub hrb h
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s hs
      obtain ⟨-, rfl⟩ := Exec.det a a'
      obtain ⟨hrd, hwr⟩ := Exec.rdwr a
      obtain ⟨u', hb', ok⟩ := tail_run hrb w
      rw [hb', Option.some.injEq, Prod.mk.injEq] at b
      obtain ⟨rfl, -⟩ := b
      exact ⟨w, a, Ends.of_tail ok hrd hwr habi.1 (Exec.keep a (noMmx_instrs hm)), ok.mem⟩
    obtain ⟨w₁, a₁, k₁, m₁⟩ := keep p₁ e₁
    obtain ⟨w₂, a₂, k₂, m₂⟩ := keep p₂ e₂
    obtain ⟨r₁, s₃₁, x₁, y₁⟩ := wiped_run h hb hnsp hd hw hpreL p₁
    obtain ⟨r₂, s₃₂, x₂, y₂⟩ := wiped_run h hb hnsp hd hw hpreL p₂
    obtain ⟨-, rfl⟩ := Exec.det a₁ y₁
    obtain ⟨-, rfl⟩ := Exec.det a₂ y₂
    have osp : s₁.gpr .esp = s₂.gpr .esp := contract_pub_sp hA hp
    -- The two runs of `c` leak the same trace, so end with the same unknowns.
    have hN : (narrow sig e n bytes false s₁).unknowns = (narrow sig e n bytes false s₂).unknowns := by
      obtain ⟨hr₁, -⟩ := argsState_run (n := n) (e := e) p₁ hb.1
      obtain ⟨hr₂, -⟩ := argsState_run (n := n) (e := e) p₂ hb.1
      have hal : (allocState bytes s₁).unknowns = (allocState bytes s₂).unknowns := hu
      exact (Exec.path (c := .block (setArgs bytes (slots sig))) (r₁ := []) (r₂ := []) (Exec.block hr₁)
        (Exec.block hr₂) (fun _ h => by simp [inames] at h)
        (by rw [allocState_esp, allocState_esp, osp]) hal).2
    have hU : s₃₁.unknowns = s₃₂.unknowns :=
      (Exec.path (r₁ := []) (r₂ := []) x₁ x₂ (fun _ hn' => by rw [inames_of_noCalls hn] at hn'; cases hn')
        (by rw [h.2.1 _ _ _ _ _ _ (narrow_pre hb.1 hpreL p₁) (narrow_pre hb.1 hpreL p₂)
          (narrow_pub hb.1 p₁ p₂ hp hleak.toL) x₁ x₂]) hN).2
    refine Ends.outside ho k₁ k₂ fun x hx => ?_
    rw [m₁, m₂]
    have su : ∀ s : State, (wipeRegs s).unknowns = s.unknowns := fun _ => rfl
    simp only [popState, osp]
    rw [su, su, hU]
    refine lose_congr ?_ _ _ _
    -- The frame before its release: the buffer zeroed, the rest as `narrow` left it.
    have hst := (pre_stackL.mp p₁).1.1
    have hEn : (s₂.gpr .esp - BitVec.ofNat 32 bytes).toNat = (s₂.gpr .esp).toNat - bytes :=
      sub_toNat (by rw [← osp]; omega_using [hst])
    simp only [zeroOn]
    split
    · rfl
    · next hz =>
      -- Outside the buffer, `c` wrote only the buffers.
      have out : ∀ {s s₃ : State} {t : List Leak}, (sig.contract abi pre post false (0 + bytes) leak).pre s →
          s.gpr .esp = s₂.gpr .esp → s.wr = s₁.wr → Exec isa c (narrow sig e n bytes false s) t s₃ →
          s₃.mem x = (narrow sig e n bytes false s).mem x := by
        intro s s₃ t hs hsp' hwr' ex
        refine ((Exec.regions ex hn).2.2 x fun r hr hc => ?_)
        obtain ⟨-, -, hwr, -⟩ := pre_stackL.mp hs
        simp only [narrow, State.withRegions_wr, List.mem_map, List.mem_filter] at hr
        obtain ⟨a, ⟨ha, hat⟩, rfl⟩ := hr
        simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ((ha | rfl) | ha) | rfl
        · -- A writable buffer.
          refine hx a.1 (List.mem_append_right _ ?_) hc
          rw [← hwr', hwr]
          exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha),
            hat⟩, rfl⟩
        · -- The buffer, which the wipe zeroed.
          apply hz
          simp only [Region.Contains, hsp'] at hc
          rw [show (s₂.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64 =
              (s₂.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 + BitVec.ofNat 64 (8 + 4 * slots sig) from
            addr_eq (by have := (s₂.gpr .esp).isLt; omega_using [hEn, hst, hb, this, osp])] at hc
          have e' := Offset.lt_iff x ((s₂.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64)
            (d := 8 + 4 * slots sig) (n := n * e.size) (by omega_using [hb])
          have := e'.mp (by omega_using [hc])
          omega_using [this, hw]
        · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hat
        · simp at hat
      rw [out p₁ osp rfl x₁, out p₂ rfl (ho.2.1.symm) x₂]
      have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := hx
      exact narrow_mem_agree hb.1 p₁ p₂ osp (args_of_pub hpub hl hp) (ho.2.2.2.2.2.2.2.2.2.2.2.2.2 x hx')

end

end VG.X86.Scrub
