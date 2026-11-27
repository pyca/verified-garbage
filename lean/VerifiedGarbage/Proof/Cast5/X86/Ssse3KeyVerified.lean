module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Key
public import VerifiedGarbage.Proof.Cast5.X86.KeyVerified
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideCore
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Cast5.X86.Ssse3KeyLit
import VerifiedGarbage.Proof.Cast5.ScrubLocal
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Cast5.X86.Ssse3Key
meta import VerifiedGarbage.Proof.Cast5.X86.KeyVerified
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideCore
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseLanes
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.CallBody
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3KeyLit
meta import VerifiedGarbage.Proof.Cast5.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Cast5.Memory

/-!
# CAST5's key expansion by `pshufb` on x86 (32-bit) meets its contract

`Impl.Cast5.X86.Ssse3.Key.expandKey`, in the order of what depends on what:
the lines over any look-ups, the look-ups' function, then the contracts.

The lines, over any look-ups (`KeyLk`: a program that leaves S5 to S8 at the
sixteen bytes of `xmm0` in the working space, `Entries`). The state of key
expansion (`KE`) is the baseline's without its table: `x` and `z` in the
working space, the subkeys so far (`Proof/Cast5/KeyMem.lean`, which states
the lines as the implementations compute them). A line is five loads
(`lineAt_ok`: `lineVal`, where the entries are those of the bytes it reads);
an array's four lines (`words_ok`) take the first from the look-ups of the
other array, whole, save the three entries of it that the next lines need
(`saveExtra_ok`), and take each next line after the look-ups of the array as
it then is (`look_ok`); the four subkeys after an array are from its
look-ups, whole (`keys_ok`). That each line reads only bytes whose entries
are there is a check of the lines' tables (`wordsOk`, `keysOk`). `halfK_ok`
is a half of §2.4 and `expandKeyWith_wp` the function, with the baseline's
entry, copy of the key and exit (`Proof/Cast5/X86/KeyVerified.lean`, whose
lemmas for them it uses).

The look-ups' function (`lookup_wp`, `call_wp`, `lookupLk : KeyLk _`), an
instruction at a time on the XMM registers: the index vectors and the rows
of the planes of S5 to S8 by the lemmas of the one-block look-ups
(`Ssse3Lookup.lean`), the planes' bytes to doublewords by those of the
sixteen blocks (`Ssse3WideCore.lean`). Only this part is about the order of
the function's instructions.

The contracts. Constant time by the taint analysis of the function with the
look-ups' function at each of its calls (`expandKey_ct`). The function
takes its working space, 848 bytes, as its fourth argument
(`expandKey_verified`); `expandKey_framed` runs it with the working space in
a frame, zeroed on return, by the frame's theorem for the signature without
that argument (`sig3`), since the `scratch` of 32 64-bit words that the
`Api` gives is too small; and `expandKey_api` gives the `Api`'s contract
from it (`Verified.narrowTo`): the regions the contract gives the function
less the caller's `scratch`, which the function neither reads nor writes,
and the argument slot that holds its address. As emitted
(`Impl.Cast5.X86.Ssse3.Key.Fn.expandKey`) it then zeroes, of the 888 bytes
of stack its contract reserves, the doublewords that the residue analysis
finds it may leave different in two runs, clears the registers a callee may
change, and returns without secret residue (`expandKey_scrubbed`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Ssse3.Key

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86
open VG.Impl.Cast5.X86.Ssse3 (ld)
open VG.Impl.Cast5.X86.Ssse3.Key
open VG.Proof.Cast5 (XZ HoldsXZ Keys KMem lineOk lineVal off_lt off_ge keys4 take_keys4 runQ runQ_succ get_runQ
  get_put)

/-! ## The look-ups' entries -/

/-- The look-ups' entries of the sixteen bytes `v`, in the working space:
`S_e` at byte `i`, for `e` from 5 to 8. -/
def Entries (m : Mem) (W : BitVec 32) (v : Nat → Byte) : Prop :=
  ∀ e, 5 ≤ e → e ≤ 8 → ∀ i < 16, m.readW (slot W (enAt e i)) 32 = Proof.Cast5.sbox e (v i)

/-- The working space: 848 bytes. -/
abbrev wS (W : BitVec 32) : Region := ⟨W.setWidth 64, 848⟩
/-- Its first 64 bytes: `x`, `z` and the saved entries. -/
abbrev loR (W : BitVec 32) : Region := ⟨W.setWidth 64, 64⟩
/-- The saved entries. -/
abbrev exR (W : BitVec 32) : Region := ⟨slot W 48, 16⟩
/-- What the look-ups write of it: the index vectors and the entries. -/
abbrev lkR (W : BitVec 32) : Region := ⟨slot W 272, 576⟩
/-- The entries. -/
abbrev enR (W : BitVec 32) : Region := ⟨slot W 592, 256⟩

theorem Entries.frame {m m' : Mem} {W : BitVec 32} {v : Nat → Byte} (h : Entries m W v) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint (enR W) r) : Entries m' W v := fun e h5 h8 i hi => by
  rw [hf.readW (r := enR W) (Offset.contains _ (by simp only [enAt]; omega) (by simp only [enAt]; omega)
    (by decide)) hd (by decide)]
  exact h e h5 h8 i hi

/-- The saved entry of line `k`. -/
def Sx (m : Mem) (W : BitVec 32) (k : Nat) (w : Spec.Cast5.Word) : Prop :=
  m.readW (slot W (extraOff + 4 * k)) 32 = w

theorem Sx.frame {m m' : Mem} {W : BitVec 32} {k : Nat} {w : Spec.Cast5.Word} (h : Sx m W k w) (hk : k < 4)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint (exR W) r) : Sx m' W k w := by
  unfold Sx
  rw [hf.readW (r := exR W) (Offset.contains _ (by simp only [extraOff]; omega) (by simp only [extraOff]; omega)
    (by decide)) hd (by decide)]
  exact h

/-- **What key expansion needs of its look-ups**: with the working space at
`esi`, writable and apart from the eight bytes of stack below `esp`, they
leave S5 to S8 at the sixteen bytes of `xmm0` in it, keep the registers but
`eax`, `ecx` and `edx`, and write only their part of the working space and
those eight bytes. -/
structure KeyLk (lk : Prog isa) : Prop where
  ok : ∀ (s : State) (W : BitVec 32), s.gpr .esi = W → W.toNat + 848 ≤ 2 ^ 32 →
    InRegions s.wr (W.setWidth 64) 848 → 8 ≤ (s.gpr .esp).toNat → Region.Disjoint (wS W) (below (s.gpr .esp) 8) →
    WP isa lk s fun t => Entries t.mem W (fun i => byte (s.xmm .xmm0) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms ∧ Frame [lkR W, below (s.gpr .esp) 8] s.mem t.mem

/-! ## The state of key expansion -/

/-- The state of key expansion from the memory `m0`: the working space at
`W` (`esi`), writable, as is the schedule `K`; `x` and `z` in it and the
subkeys so far; and what was written: its first 64 bytes, the look-ups'
part, the schedule and the eight bytes below `esp`. -/
structure KE (m0 : Mem) (W : BitVec 32) (K : Addr) (s : State) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  si : s.gpr .esi = W
  fitW : W.toNat + 848 ≤ 2 ^ 32
  wW : InRegions s.wr (W.setWidth 64) 848
  xz : HoldsXZ s.mem (W.setWidth 64) st
  keys : Keys s.mem K ws
  fr : Frame [loR W, ⟨K, 128⟩, lkR W, below (s.gpr .esp) 8] m0 s.mem
  len : ws.length ≤ 32
  wK : InRegions s.wr K 128
  dKW : Region.Disjoint ⟨K, 128⟩ (wS W)
  sp : 8 ≤ (s.gpr .esp).toNat
  dW : Region.Disjoint (wS W) (below (s.gpr .esp) 8)
  dK : Region.Disjoint ⟨K, 128⟩ (below (s.gpr .esp) 8)

section
variable {m0 : Mem} {W : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}

theorem KE.fit256 (h : KE m0 W K s st ws) : W.toNat + 256 ≤ 2 ^ 32 := by have := h.fitW; omega

theorem KE.w256 (h : KE m0 W K s st ws) : InRegions s.wr (W.setWidth 64) 256 := by
  have := CallLay.inRegions_sub h.wW (off := 0) (l := 256) (by decide) (by decide)
  rwa [BitVec.add_zero] at this

/-- A place of the working space, readable. -/
theorem KE.rd (h : KE m0 W K s st ws) {d n : Nat} (hd : d + n ≤ 848) (hn : 0 < n := by decide) :
    InRegions (s.rd ++ s.wr) (addr W d) n := by
  rw [addr_off h.fitW d (by omega)]
  obtain ⟨g, hg, hc⟩ := h.wW
  exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ hd (by decide)

/-- A place of the working space, writable. -/
theorem KE.wr (h : KE m0 W K s st ws) {d n : Nat} (hd : d + n ≤ 848) (hn : 0 < n := by decide) :
    InRegions s.wr (addr W d) n := by
  rw [addr_off h.fitW d (by omega)]
  exact CallLay.inRegions_sub h.wW hd (by decide)

theorem KE.dKlo (h : KE m0 W K s st ws) : Region.Disjoint ⟨K, 128⟩ (loR W) :=
  h.dKW.sub_right (Region.sub_prefix (by decide))

/-- The same state after a step that keeps `esi`, `esp` and the regions, and
writes within what key expansion writes. -/
theorem KE.step (h : KE m0 W K s st ws) {u : State} {st' : XZ} {ws' : List Spec.Cast5.Word}
    (hsi : u.gpr .esi = s.gpr .esi) (hsp : u.gpr .esp = s.gpr .esp) (hwr : u.wr = s.wr)
    (hxz : HoldsXZ u.mem (W.setWidth 64) st') (hk : Keys u.mem K ws') (hl : ws'.length ≤ 32)
    (hf : Frame [loR W, ⟨K, 128⟩, lkR W, below (s.gpr .esp) 8] s.mem u.mem) : KE m0 W K u st' ws' where
  si := hsi.trans h.si
  fitW := h.fitW
  wW := by rw [hwr]; exact h.wW
  xz := hxz
  keys := hk
  fr := by rw [hsp]; exact h.fr.trans hf
  len := hl
  wK := by rw [hwr]; exact h.wK
  dKW := h.dKW
  sp := by rw [hsp]; exact h.sp
  dW := by rw [hsp]; exact h.dW
  dK := by rw [hsp]; exact h.dK

/-- What the look-ups' part of the working space is apart from. -/
theorem lk_lo (W : BitVec 32) : Region.Disjoint (loR W) (lkR W) := Offset.base_disjoint _ (by decide) (by decide)

theorem ex_lk (W : BitVec 32) : Region.Disjoint (exR W) (lkR W) := Offset.disjoint _ (by decide) (by decide) (by decide)

theorem en_lo (W : BitVec 32) : Region.Disjoint (enR W) (loR W) := Offset.disjoint_base _ (by decide) (by decide)

theorem lk_sub (W : BitVec 32) : Region.Sub (lkR W) (wS W) := Offset.sub_base _ (by decide)

/-- `x`, `z` and the subkeys through a frame apart from them. -/
theorem KE.frame (h : KE m0 W K s st ws) {m' : Mem} {rs : List Region} (hf : Frame rs s.mem m')
    (hlo : ∀ r ∈ rs, Region.Disjoint (loR W) r) (hK : ∀ r ∈ rs, Region.Disjoint ⟨K, 128⟩ r) :
    HoldsXZ m' (W.setWidth 64) st ∧ Keys m' K ws := by
  refine ⟨fun a i hi => ?_, fun i hi => ?_⟩
  · have := off_lt a
    rw [hf.bytes (R := loR W) hlo (show (64 : Nat) ≤ 2 ^ 64 by decide) (show off a + i < 64 by omega)]
    exact h.xz a i hi
  · have := h.len
    rw [hf.readW (r := ⟨K, 128⟩) (Offset.contains_base _ (by omega) (by omega)) hK (by decide)]
    exact h.keys i hi

end

/-! ## A line -/

section
variable {m0 : Mem} {W : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}

/-- The registers a line writes. -/
def lineRegsK : List Reg := [.eax, .ecx]

/-- A write of a word, as a frame. -/
theorem frame_write (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) : Frame [⟨a, w / 8⟩] m (m.writeW a v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

/-- The state after a step that writes memory as `KMem` states it. -/
theorem KE.ofKMem (h : KE m0 W K s st ws) {u : State} {st' : XZ} {ws' : List Spec.Cast5.Word}
    (k : KMem s.mem u.mem (W.setWidth 64) K st' ws') (hl : ws'.length ≤ 32) (hsi : u.gpr .esi = s.gpr .esi)
    (hsp : u.gpr .esp = s.gpr .esp) (hwr : u.wr = s.wr) : KE m0 W K u st' ws' :=
  h.step hsi hsp hwr k.xz k.keys hl (k.fr.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl))

/-- **A line**: the exclusive or of five loads, and of its quadruple, is
the line's value, where the entries are those of the bytes it reads. -/
theorem lineAt_ok (h : KE m0 W K s st ws) (l : Impl.Cast5.Line) (hl : lineOk l = true) {v : Nat → Byte}
    (hE : Entries s.mem W v) (h1 : v l.main.1.2 = st.get l.main.1) (h2 : v l.main.2.1.2 = st.get l.main.2.1)
    (h3 : v l.main.2.2.1.2 = st.get l.main.2.2.1) (h4 : v l.main.2.2.2.2 = st.get l.main.2.2.2) {xo : Nat}
    (hxo : xo + 4 ≤ 848) (hx : s.mem.readW (slot W xo) 32 = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2)) :
    WP isa (.block (lineAt l xo)) s fun u =>
      (u.gpr .eax = lineVal st l ∧ u.mem = s.mem ∧ u.syms = s.syms) ∧ Keep lineRegsK s u := by
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, _⟩, _⟩, hwd⟩ := hl
  have tw : writesOnly lineRegsK (.block (lineAt l xo)) = true := by
    unfold lineAt mains lineWord
    rcases l.word with _ | ⟨a, q⟩ <;> rfl
  refine WP.keep lineRegsK ?_ tw
  have fW := h.fitW
  have en (e i : Nat) (h5 : 5 ≤ e) (h8 : e ≤ 8) (hi : i < 16) :
      s.mem.readW (addr W (enAt e i)) 32 = Proof.Cast5.sbox e (v i) := by
    rw [addr_off fW _ (by simp only [enAt]; omega)]; exact hE e h5 h8 i hi
  have r8 := h.rd (d := enAt 8 l.main.2.2.2.2) (n := 4) (by simp only [enAt]; omega)
  have r7 := h.rd (d := enAt 7 l.main.2.2.1.2) (n := 4) (by simp only [enAt]; omega)
  have r6 := h.rd (d := enAt 6 l.main.2.1.2) (n := 4) (by simp only [enAt]; omega)
  have r5 := h.rd (d := enAt 5 l.main.1.2) (n := 4) (by simp only [enAt]; omega)
  have e8 : s.mem.readW (addr W (enAt 8 l.main.2.2.2.2)) 32 = Spec.Cast5.S8 (st.get l.main.2.2.2) := by
    rw [en 8 _ (by decide) (by decide) hd, h4]; rfl
  have e7 : s.mem.readW (addr W (enAt 7 l.main.2.2.1.2)) 32 = Spec.Cast5.S7 (st.get l.main.2.2.1) := by
    rw [en 7 _ (by decide) (by decide) hc, h3]; rfl
  have e6 : s.mem.readW (addr W (enAt 6 l.main.2.1.2)) 32 = Spec.Cast5.S6 (st.get l.main.2.1) := by
    rw [en 6 _ (by decide) (by decide) hb, h2]; rfl
  have e5 : s.mem.readW (addr W (enAt 5 l.main.1.2)) 32 = Spec.Cast5.S5 (st.get l.main.1) := by
    rw [en 5 _ (by decide) (by decide) ha, h1]; rfl
  have rx := h.rd (d := xo) (n := 4) hxo
  have ex : s.mem.readW (addr W xo) 32 = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2) := by
    rw [addr_off fW _ (by omega)]; exact hx
  unfold lineAt mains lineWord
  rcases hwd' : l.word with _ | ⟨a, q⟩
  · crun [h.si, r8, r7, r6, r5, rx, e8, e7, e6, e5, ex, List.append_nil]
    simp only [lineVal, hwd']
  · have hq : q < 4 := by rw [hwd'] at hwd; simpa using hwd
    have := off_lt a
    have rq := h.rd (d := off a + 4 * q) (n := 4) (by omega)
    have eq : byteRev32 (s.mem.readW (addr W (off a + 4 * q)) 32) = Proof.Cast5.quadOf (st.arr a) q := by
      rw [addr_off fW _ (by omega)]; exact h.xz.quad a hq
    crun [h.si, r8, r7, r6, r5, rx, rq, e8, e7, e6, e5, ex, bswap_eq, eq]
    simp only [lineVal, hwd']

/-- The state after a line, which writes no memory. -/
theorem KE.afterLine (h : KE m0 W K s st ws) {u : State} (um : u.mem = s.mem) (uk : Keep lineRegsK s u) :
    KE m0 W K u st ws :=
  h.step (uk.gpr _ (by decide)) (uk.gpr _ (by decide)) uk.wr (by rw [um]; exact h.xz) (by rw [um]; exact h.keys)
    h.len (by rw [um]; exact Frame.refl _ _)

/-- A line stored as quadruple `q` of the array `a`: the entries and the
saved entries stay. -/
theorem lineQ_ok (h : KE m0 W K s st ws) (l : Impl.Cast5.Line) (hl : lineOk l = true) {v : Nat → Byte}
    (hE : Entries s.mem W v) (h1 : v l.main.1.2 = st.get l.main.1) (h2 : v l.main.2.1.2 = st.get l.main.2.1)
    (h3 : v l.main.2.2.1.2 = st.get l.main.2.2.1) (h4 : v l.main.2.2.2.2 = st.get l.main.2.2.2) {xo : Nat}
    (hxo : xo + 4 ≤ 848) (hx : s.mem.readW (slot W xo) 32 = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2))
    (a : Arr) {q : Nat} (hq : q < 4) :
    WP isa (.block (lineAt l xo ++ storeQuad a q)) s fun u =>
      KE m0 W K u (st.put a q (lineVal st l)) ws ∧ Entries u.mem W v ∧
      (∀ k x, k < 4 → Sx s.mem W k x → Sx u.mem W k x) ∧ u.syms = s.syms ∧ Keep lineRegsK s u := by
  rw [WP.block_append_iff]
  refine WP.mono (lineAt_ok h l hl hE h1 h2 h3 h4 hxo hx) fun u ⟨⟨uax, um, usy⟩, uk⟩ => ?_
  have := off_lt a
  have hu := h.afterLine um uk
  refine WP.mono (storeQuad_ok u hu.si a q uax (hu.wr (by omega))) fun w ⟨wm, wg, wrd, wwr, wsy⟩ => ?_
  rw [addr_off hu.fitW _ (by omega)] at wm
  have km := KMem.quad ⟨hu.xz, hu.keys, Frame.refl _ _⟩ hu.dKlo hu.len a hq (lineVal st l)
  rw [← wm] at km
  have fw : Frame [⟨slot W (off a + 4 * q), 32 / 8⟩] u.mem w.mem := by rw [wm]; exact frame_write _ _ _
  refine ⟨hu.ofKMem km hu.len (wg _ (by decide)) (wg _ (by decide)) wwr, ?_, fun k x hk hs => ?_, wsy.trans usy,
    ⟨fun r hr => ?_, wrd.trans uk.rd, wwr.trans uk.wr⟩⟩
  · refine (show Entries u.mem W v by rw [um]; exact hE).frame fw fun r hr => ?_
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by decide) (by omega)
  · refine (show Sx u.mem W k x by unfold Sx; rw [um]; exact hs).frame hk fw fun r hr => ?_
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by decide) (by omega)
  · rw [wg r (fun e => hr (e ▸ List.mem_cons_self)), uk.gpr r hr]

/-- A line stored as the next subkey, `k` of those from `edi`. -/
theorem lineK_ok (h : KE m0 W K s st ws) (l : Impl.Cast5.Line) (hl : lineOk l = true) {v : Nat → Byte}
    (hE : Entries s.mem W v) (h1 : v l.main.1.2 = st.get l.main.1) (h2 : v l.main.2.1.2 = st.get l.main.2.1)
    (h3 : v l.main.2.2.1.2 = st.get l.main.2.2.1) (h4 : v l.main.2.2.2.2 = st.get l.main.2.2.2) {xo : Nat}
    (hxo : xo + 4 ≤ 848) (hx : s.mem.readW (slot W xo) 32 = Proof.Cast5.sbox l.extra.1 (st.get l.extra.2))
    {k : Nat} {E : BitVec 32} (hdi : s.gpr .edi = E)
    (hadr : addr E (4 * k) = K + BitVec.ofNat 64 (4 * ws.length)) (hlen : ws.length < 32) :
    WP isa (.block (lineAt l xo ++ storeKey k)) s fun u =>
      KE m0 W K u st (ws ++ [lineVal st l]) ∧ Entries u.mem W v ∧ u.syms = s.syms ∧ Keep lineRegsK s u := by
  rw [WP.block_append_iff]
  refine WP.mono (lineAt_ok h l hl hE h1 h2 h3 h4 hxo hx) fun u ⟨⟨uax, um, usy⟩, uk⟩ => ?_
  have hu := h.afterLine um uk
  have hw : InRegions u.wr (addr E (4 * k)) 4 := by
    rw [hadr]; exact CallLay.inRegions_sub hu.wK (by omega) (by decide)
  refine WP.mono (storeKey_ok u (by rw [uk.gpr .edi (by decide), hdi]) k uax hw)
    fun w ⟨wm, wg, wrd, wwr, wsy⟩ => ?_
  rw [hadr] at wm
  have km := KMem.key ⟨hu.xz, hu.keys, Frame.refl _ _⟩ hu.dKlo hlen (lineVal st l)
  rw [← wm] at km
  have fw : Frame [⟨K + BitVec.ofNat 64 (4 * ws.length), 32 / 8⟩] u.mem w.mem := by rw [wm]; exact frame_write _ _ _
  refine ⟨hu.ofKMem km (by rw [List.length_append, List.length_singleton]; omega) (by rw [wg]) (by rw [wg]) wwr,
    ?_, wsy.trans usy, ⟨fun r hr => by rw [wg, uk.gpr r hr], wrd.trans uk.rd, wwr.trans uk.wr⟩⟩
  refine (show Entries u.mem W v by rw [um]; exact hE).frame fw fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact ((hu.dKW.sub_left (Offset.sub_base K (by omega))).symm).sub_left (Offset.sub_base _ (by decide))

/-- An entry saved for a later line. -/
theorem saveExtra_ok (h : KE m0 W K s st ws) {v : Nat → Byte} (hE : Entries s.mem W v) (ls : List Impl.Cast5.Line) {k : Nat}
    (hk : k < 4) (he5 : 5 ≤ (ls.getD k default).extra.1) (he8 : (ls.getD k default).extra.1 ≤ 8)
    (hf : (ls.getD k default).extra.2.2 < 16) :
    WP isa (.block (saveExtra ls k)) s fun u => KE m0 W K u st ws ∧ Entries u.mem W v ∧
      Sx u.mem W k (Proof.Cast5.sbox (ls.getD k default).extra.1 (v (ls.getD k default).extra.2.2)) ∧
      (∀ k' x, k' < 4 → k' ≠ k → Sx s.mem W k' x → Sx u.mem W k' x) ∧ u.syms = s.syms ∧ Keep lineRegsK s u := by
  have fW := h.fitW
  have r := h.rd (d := enAt (ls.getD k default).extra.1 (ls.getD k default).extra.2.2) (n := 4)
    (by simp only [enAt]; omega)
  have e : s.mem.readW (addr W (enAt (ls.getD k default).extra.1 (ls.getD k default).extra.2.2)) 32 =
      Proof.Cast5.sbox (ls.getD k default).extra.1 (v (ls.getD k default).extra.2.2) := by
    rw [addr_off fW _ (by simp only [enAt]; omega)]; exact hE _ he5 he8 _ hf
  have w := h.wr (d := extraOff + 4 * k) (n := 4) (by simp only [extraOff]; omega)
  have run : WP isa (.block (saveExtra ls k)) s fun u =>
      (u.mem = s.mem.writeW (addr W (extraOff + 4 * k))
        (Proof.Cast5.sbox (ls.getD k default).extra.1 (v (ls.getD k default).extra.2.2)) ∧ u.syms = s.syms) := by
    unfold saveExtra
    crun [h.si, r, e, w]
  refine WP.mono (WP.keep lineRegsK run rfl) fun u ⟨⟨um, usy⟩, uk⟩ => ?_
  rw [addr_off fW _ (by simp only [extraOff]; omega)] at um
  have km := KMem.write ⟨h.xz, h.keys, Frame.refl _ _⟩ h.dKlo h.len (d := extraOff + 4 * k)
    (Proof.Cast5.sbox (ls.getD k default).extra.1 (v (ls.getD k default).extra.2.2))
    (by simp only [extraOff]; omega) (.inr (by simp only [extraOff]; omega))
  rw [← um] at km
  have fw : Frame [⟨slot W (extraOff + 4 * k), 32 / 8⟩] s.mem u.mem := by rw [um]; exact frame_write _ _ _
  refine ⟨h.ofKMem km h.len (uk.gpr _ (by decide)) (uk.gpr _ (by decide)) uk.wr, ?_, ?_, fun k' x hk' hne hs => ?_,
    usy, uk⟩
  · refine hE.frame fw fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by simp only [extraOff]; omega)) (by decide) (by simp only [extraOff]; omega)
  · unfold Sx; rw [um]; exact Mem.readW_writeW_self32 _ _ _
  · unfold Sx at hs ⊢
    rw [um, Mem.readW_writeW_sep (Offset.sep _ (by simp only [extraOff]; omega) (by simp only [extraOff]; omega)
      (by simp only [extraOff]; omega)) (by decide)]
    exact hs

theorem Entries.congr {m : Mem} {v v' : Nat → Byte} (h : Entries m W v) (hv : ∀ i < 16, v i = v' i) :
    Entries m W v' := fun e h5 h8 i hi => by rw [← hv i hi]; exact h e h5 h8 i hi

/-- **The look-ups of an array as it is**: its entries; `x`, `z`, the
subkeys and the saved entries stay. -/
theorem look_ok {lk : Prog isa} (hlk : KeyLk lk) (h : KE m0 W K s st ws) (a : Arr) :
    WP isa (look lk a) s fun u => KE m0 W K u st ws ∧ Entries u.mem W (st.arr a) ∧
      (∀ k x, k < 4 → Sx s.mem W k x → Sx u.mem W k x) ∧ u.syms = s.syms ∧ Keep [.eax, .ecx, .edx] s u := by
  have := off_lt a
  have fW := h.fitW
  have r := h.rd (d := off a) (n := 16) (by omega)
  have ld1 : WP isa (.block [ld .xmm0 .esi (off a)]) s fun u =>
      u.xmm .xmm0 = s.mem.readW (addr W (off a)) 128 ∧ u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧
        u.wr = s.wr ∧ u.syms = s.syms := by
    unfold ld
    crun [h.si, r]
  unfold look
  refine WP.seq (WP.mono ld1 fun u ⟨ux, um, ug, urd, uwr, usy⟩ => ?_)
  have hu : KE m0 W K u st ws := h.step (by rw [ug]) (by rw [ug]) uwr (by rw [um]; exact h.xz)
    (by rw [um]; exact h.keys) h.len (by rw [um]; exact Frame.refl _ _)
  refine WP.mono (hlk.ok u W hu.si hu.fitW hu.wW hu.sp hu.dW) fun t ⟨tE, tg, trd, twr, tsy, tf⟩ => ?_
  have usp : u.gpr .esp = s.gpr .esp := by rw [ug]
  rw [um, usp] at tf
  obtain ⟨txz, tk⟩ := h.frame tf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact lk_lo W
      · exact h.dW.sub_left (Region.sub_prefix (by decide))) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.dKW.sub_right (lk_sub W)
      · exact h.dK)
  refine ⟨h.step ((tg _ (by decide) (by decide) (by decide)).trans (by rw [ug]))
      ((tg _ (by decide) (by decide) (by decide)).trans usp) (twr.trans uwr) txz tk h.len
      (tf.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inr (.inr (.inl rfl))
        · exact .inr (.inr (.inr rfl))), tE.congr fun i hi => ?_, fun k x hk hs => ?_, tsy.trans usy,
    ⟨fun r hr => ?_, trd.trans urd, twr.trans uwr⟩⟩
  · rw [ux, addr_off fW _ (by omega), byte, VG.X86.byte_readW _ _ (by omega), Offset.add_add]
    exact h.xz a i hi
  · refine hs.frame hk tf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ex_lk W
    · exact h.dW.sub_left (Offset.sub_base _ (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [tg r hr.1 hr.2.1 hr.2.2, ug]

end

/-! ## An array's four lines, and four subkeys -/

/-- The other array. -/
def other : Arr → Arr
  | .x => .z
  | .z => .x

/-- A line that key expansion can run: its main bytes are in the array `m`
and its extra one in `e`. -/
def lineIn (l : Impl.Cast5.Line) (m e : Arr) : Bool :=
  lineOk l && l.main.1.1 == m && l.main.2.1.1 == m && l.main.2.2.1.1 == m && l.main.2.2.2.1 == m &&
    l.extra.2.1 == e && decide (l.extra.2.2 < 16)

/-- The four lines of the array `a`: the first is of the other array's
bytes, the next three of its own, each with an extra one of the other's. -/
def wordsOk (a : Arr) (ls : List Impl.Cast5.Line) : Bool :=
  lineIn (ls.getD 0 default) (other a) (other a) && lineIn (ls.getD 1 default) a (other a) &&
    lineIn (ls.getD 2 default) a (other a) && lineIn (ls.getD 3 default) a (other a)

/-- Four subkeys' lines, of the bytes of the array `c`. -/
def keysOk (c : Arr) (ls : List Impl.Cast5.Line) : Bool :=
  lineIn (ls.getD 0 default) c c && lineIn (ls.getD 1 default) c c && lineIn (ls.getD 2 default) c c &&
    lineIn (ls.getD 3 default) c c

theorem XZ_get (st : XZ) (p : Pos) : st.get p = st.arr p.1 p.2 := by
  obtain ⟨a, i⟩ := p; cases a <;> rfl

theorem other_ne (a : Arr) : other a ≠ a := by cases a <;> decide

/-- What `lineIn` gives: the line is well formed, and its bytes are the
arrays'. -/
theorem lineIn_spec {l : Impl.Cast5.Line} {m e : Arr} (h : lineIn l m e = true) (st : XZ) :
    lineOk l = true ∧ st.arr m l.main.1.2 = st.get l.main.1 ∧ st.arr m l.main.2.1.2 = st.get l.main.2.1 ∧
      st.arr m l.main.2.2.1.2 = st.get l.main.2.2.1 ∧ st.arr m l.main.2.2.2.2 = st.get l.main.2.2.2 ∧
      st.arr e l.extra.2.2 = st.get l.extra.2 ∧ l.extra.2.1 = e ∧ l.extra.2.2 < 16 ∧
      5 ≤ l.extra.1 ∧ l.extra.1 ≤ 8 := by
  simp only [lineIn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨ok, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
  have ok' := ok
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at ok'
  refine ⟨ok, ?_, ?_, ?_, ?_, ?_, a5, a6, ok'.1.1.2, ok'.1.2⟩
  · rw [XZ_get, a1]
  · rw [XZ_get, a2]
  · rw [XZ_get, a3]
  · rw [XZ_get, a4]
  · rw [XZ_get, a5]

section
variable {m0 : Mem} {W : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}

/-- The registers the look-ups and the lines write. -/
def lookRegs : List Reg := [.eax, .ecx, .edx]

theorem keepL {s u : State} (k : Keep lineRegsK s u) : Keep lookRegs s u :=
  ⟨fun r hr => k.gpr r fun h => hr (by
    simp only [lineRegsK, lookRegs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)), k.rd, k.wr⟩

/-- A line of an array after its first: the look-ups of the array as it is,
then the line, with its saved entry, stored as quadruple `k`. -/
theorem wordStep {lk : Prog isa} (hlk : KeyLk lk) (h : KE m0 W K s st ws) (a : Arr) {l : Impl.Cast5.Line}
    (hin : lineIn l a (other a) = true) {k : Nat} (hk : k < 4)
    (hsx : Sx s.mem W k (Proof.Cast5.sbox l.extra.1 (st.get l.extra.2))) {rest : Prog isa} {Q : State → Prop}
    (cont : ∀ u, KE m0 W K u (st.put a k (lineVal st l)) ws →
      (∀ k' x, k' < 4 → Sx s.mem W k' x → Sx u.mem W k' x) → u.syms = s.syms → Keep lookRegs s u →
      WP isa rest u Q) :
    WP isa (.seq (look lk a) (.seq (.block (lineS l k ++ storeQuad a k)) rest)) s Q := by
  obtain ⟨ok, h1, h2, h3, h4, -, -, -, -, -⟩ := lineIn_spec hin st
  refine WP.seq (WP.mono (look_ok hlk h a) fun u ⟨hu, uE, usx, usy, uk⟩ => ?_)
  refine WP.seq (WP.mono (lineQ_ok hu l ok uE h1 h2 h3 h4 (xo := extraOff + 4 * k) (by simp only [extraOff]; omega)
    (usx k _ hk hsx) a hk) fun w ⟨hw, _, wsx, wsy, wk⟩ => ?_)
  exact cont w hw (fun k' x hk' hs => wsx k' x hk' (usx k' x hk' hs)) (wsy.trans usy) (uk.trans (keepL wk))

/-- **The four lines of an array**, after the look-ups of the other array,
whole: the array, and its look-ups, whole. -/
theorem words_ok {lk : Prog isa} (hlk : KeyLk lk) (h : KE m0 W K s st ws) (a : Arr) {ls : List Impl.Cast5.Line}
    (hg : wordsOk a ls = true) (hE : Entries s.mem W (st.arr (other a))) :
    WP isa (words lk a ls) s fun u => KE m0 W K u (runQ a ls 4 st) ws ∧
      Entries u.mem W ((runQ a ls 4 st).arr a) ∧ u.syms = s.syms ∧ Keep lookRegs s u := by
  simp only [wordsOk, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨g0, g1⟩, g2⟩, g3⟩ := hg
  obtain ⟨ok0, a1, a2, a3, a4, a5, -, f0, e50, e80⟩ := lineIn_spec g0 st
  obtain ⟨-, -, -, -, -, x1, o1, f1, e51, e81⟩ := lineIn_spec g1 st
  obtain ⟨-, -, -, -, -, x2, o2, f2, e52, e82⟩ := lineIn_spec g2 st
  obtain ⟨-, -, -, -, -, x3, o3, f3, e53, e83⟩ := lineIn_spec g3 st
  -- a byte of the other array, through the lines of this one
  have hget (k : Nat) {p : Pos} (hp : p.1 = other a) : (runQ a ls k st).get p = st.get p :=
    get_runQ a ls k st (by rw [hp]; exact other_ne a)
  unfold words
  rw [show saveExtra ls 1 ++ saveExtra ls 2 ++ saveExtra ls 3 ++ lineE (ls.getD 0 default) ++ storeQuad a 0 =
      saveExtra ls 1 ++ (saveExtra ls 2 ++ (saveExtra ls 3 ++ (lineAt (ls.getD 0 default)
        (enAt (ls.getD 0 default).extra.1 (ls.getD 0 default).extra.2.2) ++ storeQuad a 0))) by
    simp only [List.append_assoc, lineE]]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveExtra_ok h hE ls (k := 1) (by decide) e51 e81 f1) fun u1 ⟨h1, E1, s11, _, sy1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveExtra_ok h1 E1 ls (k := 2) (by decide) e52 e82 f2) fun u2 ⟨h2, E2, s22, k2o, sy2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveExtra_ok h2 E2 ls (k := 3) (by decide) e53 e83 f3) fun u3 ⟨h3, E3, s33, k3o, sy3, k3⟩ => ?_
  have s31 := k3o 1 _ (by decide) (by decide) (k2o 1 _ (by decide) (by decide) s11)
  have s32 := k3o 2 _ (by decide) (by decide) s22
  rw [x1] at s31
  rw [x2] at s32
  rw [x3] at s33
  refine WP.mono (lineQ_ok h3 _ ok0 E3 a1 a2 a3 a4 (by simp only [enAt]; omega)
    ((E3 _ e50 e80 _ f0).trans (by rw [a5])) a (q := 0) (by decide)) fun v0 ⟨hv0, _, sx0, sy0, kv0⟩ => ?_
  have r1 : runQ a ls 1 st = st.put a 0 (lineVal st (ls.getD 0 default)) := runQ_succ a ls 0 st
  rw [← r1] at hv0
  have keep0 : Keep lookRegs s v0 := (((keepL k1).trans (keepL k2)).trans (keepL k3)).trans (keepL kv0)
  have sy0' : v0.syms = s.syms := sy0.trans (sy3.trans (sy2.trans sy1))
  refine wordStep hlk hv0 a g1 (by decide)
    (by rw [hget 1 o1]; exact sx0 1 _ (by decide) s31) fun w1 hw1 sx1 sy1' kw1 => ?_
  rw [← runQ_succ] at hw1
  refine wordStep hlk hw1 a g2 (by decide)
    (by rw [hget 2 o2]; exact sx1 2 _ (by decide) (sx0 2 _ (by decide) s32)) fun w2 hw2 sx2 sy2' kw2 => ?_
  rw [← runQ_succ] at hw2
  refine wordStep hlk hw2 a g3 (by decide)
    (by rw [hget 3 o3]; exact sx2 3 _ (by decide) (sx1 3 _ (by decide) (sx0 3 _ (by decide) s33)))
    fun w3 hw3 _ sy3' kw3 => ?_
  rw [← runQ_succ] at hw3
  refine WP.mono (look_ok hlk hw3 a) fun t ⟨ht, tE, _, tsy, tk⟩ => ⟨ht, tE, ?_, ?_⟩
  · rw [tsy, sy3', sy2', sy1', sy0']
  · exact (((keep0.trans kw1).trans kw2).trans kw3).trans tk

theorem keys_eq (ls : List Impl.Cast5.Line) (b : Nat) (is : List Instr) : keys ls b ++ is =
    lineAt (ls.getD 0 default) (enAt (ls.getD 0 default).extra.1 (ls.getD 0 default).extra.2.2) ++ storeKey (b + 0) ++
    (lineAt (ls.getD 1 default) (enAt (ls.getD 1 default).extra.1 (ls.getD 1 default).extra.2.2) ++ storeKey (b + 1) ++
    (lineAt (ls.getD 2 default) (enAt (ls.getD 2 default).extra.1 (ls.getD 2 default).extra.2.2) ++ storeKey (b + 2) ++
    (lineAt (ls.getD 3 default) (enAt (ls.getD 3 default).extra.1 (ls.getD 3 default).extra.2.2) ++ storeKey (b + 3) ++
      is))) := by
  simp only [keys, lineE, show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-- **Four subkeys**, from the look-ups of the array `c`, whole: stored from
`b` on at `edi`, which is at `K + 64 hh`. -/
theorem keys_ok (h : KE m0 W K s st ws) (c : Arr) {ls : List Impl.Cast5.Line} (hg : keysOk c ls = true)
    (hE : Entries s.mem W (st.arr c)) {b hh : Nat} {E : BitVec 32} (hdi : s.gpr .edi = E)
    (hEa : ∀ k < 16, addr E (4 * k) = K + BitVec.ofNat 64 (64 * hh + 4 * k)) (hlen : ws.length = 16 * hh + b)
    (hle : ws.length + 4 ≤ 32) (hb : b + 4 ≤ 16) {is : List Instr} {Q : State → Prop}
    (cont : ∀ u, KE m0 W K u st (ws ++ keys4 ls st) → Entries u.mem W (st.arr c) → u.syms = s.syms →
      Keep lineRegsK s u → WP isa (.block is) u Q) :
    WP isa (.block (keys ls b ++ is)) s Q := by
  simp only [keysOk, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨g0, g1⟩, g2⟩, g3⟩ := hg
  have step {u : State} {k : Nat} (hk : k < 4) (gk : lineIn (ls.getD k default) c c = true)
      (hu : KE m0 W K u st (ws ++ (keys4 ls st).take k)) (uE : Entries u.mem W (st.arr c))
      (ud : u.gpr .edi = E) {is' : List Instr} {Q' : State → Prop}
      (cont' : ∀ w, KE m0 W K w st (ws ++ (keys4 ls st).take (k + 1)) → Entries w.mem W (st.arr c) →
        w.syms = u.syms → Keep lineRegsK u w → WP isa (.block is') w Q') :
      WP isa (.block (lineAt (ls.getD k default)
        (enAt (ls.getD k default).extra.1 (ls.getD k default).extra.2.2) ++ storeKey (b + k) ++ is')) u Q' := by
    obtain ⟨ok, h1, h2, h3, h4, h5, -, f, e5, e8⟩ := lineIn_spec gk st
    have hl : (ws ++ (keys4 ls st).take k).length = ws.length + k := by
      rw [List.length_append, List.length_take, show (keys4 ls st).length = 4 from rfl, Nat.min_eq_left (by omega)]
    rw [WP.block_append_iff]
    refine WP.mono (lineK_ok hu _ ok uE h1 h2 h3 h4 (by simp only [enAt]; omega)
      ((uE _ e5 e8 _ f).trans (by rw [h5])) (k := b + k) ud
      (by rw [hEa _ (by omega), hl, hlen]; congr 2; omega) (by rw [hl]; omega)) fun w ⟨hw, wE, wsy, wk⟩ => ?_
    exact cont' w (by rw [take_keys4 _ _ hk, ← List.append_assoc]; exact hw) wE wsy wk
  rw [keys_eq]
  refine step (k := 0) (by decide) g0 (by rw [List.take_zero, List.append_nil]; exact h) hE hdi
    fun u1 h1 E1 sy1 k1 => ?_
  refine step (k := 1) (by decide) g1 h1 E1 ((k1.gpr _ (by decide)).trans hdi) fun u2 h2 E2 sy2 k2 => ?_
  refine step (k := 2) (by decide) g2 h2 E2 ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans hdi))
    fun u3 h3 E3 sy3 k3 => ?_
  refine step (k := 3) (by decide) g3 h3 E3
    ((k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans hdi)))
    fun u4 h4 E4 sy4 k4 => ?_
  exact cont u4 h4 E4 (by rw [sy4, sy3, sy2, sy1]) (((k1.trans k2).trans k3).trans k4)

end

/-! ## A half -/

open VG.Proof.Cast5 (halfImpl runZ runX runQ_z runQ_x halves halves_length halves_two bytesAt_getD scheduleAt_keys)

theorem wZ : wordsOk .z zLines = true := by decide
theorem wX : wordsOk .x xLines = true := by decide
theorem kA : keysOk .z aLines = true := by decide
theorem kB : keysOk .x bLines = true := by decide
theorem kC : keysOk .z cLines = true := by decide
theorem kD : keysOk .x dLines = true := by decide

/-- The registers a half writes. -/
def halfRegs : List Reg := [.eax, .ecx, .edx, .edi, .ebx]

theorem keepH {s u : State} (k : Keep lookRegs s u) : Keep halfRegs s u :=
  ⟨fun r hr => k.gpr r fun h => hr (by
    simp only [halfRegs, lookRegs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))), k.rd, k.wr⟩

/-- The end of a half: `edi` on, and the count of halves down. -/
theorem halfEnd_ok (u : State) {E b : BitVec 32} (hdi : u.gpr .edi = E) (hbx : u.gpr .ebx = b) :
    WP isa (.block [.alu .add .edi (imm 64), .alu .sub .ebx (imm 1)]) u fun v =>
      v.gpr .edi = E + BitVec.ofNat 32 64 ∧ v.gpr .ebx = b - 1 ∧ v.zf = some (b - 1 == 0) ∧ v.mem = u.mem ∧
        (∀ r, r ≠ .edi → r ≠ .ebx → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms := by
  crun [hdi, hbx]
  exact ⟨rfl, rfl, fun r h1 h2 => by simp only [h1, h2, ite_false]⟩

section
variable {m0 : Mem} {W : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}

/-- **A half of §2.4**, after the look-ups of `x`: its sixteen subkeys, the
arrays it leaves, and the look-ups of the new `x`. -/
theorem halfK_ok {lk : Prog isa} (hlk : KeyLk lk) (h : KE m0 W K s st ws) (hE : Entries s.mem W st.x) {hh : Nat}
    {K32 : BitVec 32} (hK : K = K32.setWidth 64) (hfitK : K32.toNat + 128 ≤ 2 ^ 32)
    (hdi : s.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh)) (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa (Impl.Cast5.X86.Ssse3.Key.half lk) s fun u => KE m0 W K u (halfImpl st).2 (ws ++ (halfImpl st).1) ∧
      Entries u.mem W (halfImpl st).2.x ∧ u.gpr .edi = K32 + BitVec.ofNat 32 (64 * (hh + 1)) ∧
      u.gpr .ebx = s.gpr .ebx - 1 ∧ u.zf = some (s.gpr .ebx - 1 == 0) ∧ u.syms = s.syms ∧ Keep halfRegs s u := by
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (keys4 ls t).length = 4 := rfl
  obtain hEa : ∀ k < 16, addr (K32 + BitVec.ofNat 32 (64 * hh)) (4 * k) =
      K + BitVec.ofNat 64 (64 * hh + 4 * k) := by
    intro k hk
    rw [hK, show addr (K32 + BitVec.ofNat 32 (64 * hh)) (4 * k) = addr K32 (64 * hh + 4 * k) by
      simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact addr_eq (by omega)
  have kd {u v : State} (k : Keep lookRegs u v) : v.gpr .edi = u.gpr .edi := k.gpr _ (by decide)
  have kl {u v : State} (k : Keep lineRegsK u v) : v.gpr .edi = u.gpr .edi := k.gpr _ (by decide)
  unfold Impl.Cast5.X86.Ssse3.Key.half
  refine WP.seq (WP.mono (words_ok hlk h .z wZ hE) fun u1 ⟨h1, E1, s1, k1⟩ => ?_)
  rw [runQ_z] at h1 E1
  refine WP.seq ?_
  rw [← List.append_nil (keys aLines 0)]
  refine keys_ok h1 .z kA E1 (b := 0) (hh := hh) ((kd k1).trans hdi) hEa (by rw [hlen]; rfl) (by omega) (by decide)
    fun u2 h2 E2 s2 k2 => WP.block_nil ?_
  refine WP.seq (WP.mono (words_ok hlk h2 .x wX E2) fun u3 ⟨h3, E3, s3, k3⟩ => ?_)
  rw [runQ_x] at h3 E3
  refine WP.seq ?_
  rw [← List.append_nil (keys bLines 4)]
  refine keys_ok h3 .x kB E3 (b := 4) (hh := hh) ((kd k3).trans ((kl k2).trans ((kd k1).trans hdi))) hEa
    (by rw [List.length_append, hlen, l4]) (by rw [List.length_append, hlen, l4]; omega) (by decide)
    fun u4 h4 E4 s4 k4 => WP.block_nil ?_
  refine WP.seq (WP.mono (words_ok hlk h4 .z wZ E4) fun u5 ⟨h5, E5, s5, k5⟩ => ?_)
  rw [runQ_z] at h5 E5
  refine WP.seq ?_
  rw [← List.append_nil (keys cLines 8)]
  refine keys_ok h5 .z kC E5 (b := 8) (hh := hh)
    ((kd k5).trans ((kl k4).trans ((kd k3).trans ((kl k2).trans ((kd k1).trans hdi))))) hEa
    (by rw [List.length_append, List.length_append, hlen, l4, l4])
    (by rw [List.length_append, List.length_append, hlen, l4, l4]; omega) (by decide)
    fun u6 h6 E6 s6 k6 => WP.block_nil ?_
  refine WP.seq (WP.mono (words_ok hlk h6 .x wX E6) fun u7 ⟨h7, E7, s7, k7⟩ => ?_)
  rw [runQ_x] at h7 E7
  obtain k17 : Keep halfRegs s u7 := (((((keepH k1).trans (keepH (keepL k2))).trans (keepH k3)).trans
    (keepH (keepL k4))).trans (keepH k5)).trans (keepH (keepL k6)) |>.trans (keepH k7)
  refine keys_ok h7 .x kD E7 (b := 12) (hh := hh)
    ((kd k7).trans ((kl k6).trans ((kd k5).trans ((kl k4).trans ((kd k3).trans ((kl k2).trans
      ((kd k1).trans hdi))))))) hEa
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega) (by decide)
    fun u8 h8 E8 s8 k8 => ?_
  obtain k18 : Keep halfRegs s u8 := k17.trans (keepH (keepL k8))
  obtain hdi8 : u8.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh) :=
    (kl k8).trans ((kd k7).trans ((kl k6).trans ((kd k5).trans ((kl k4).trans ((kd k3).trans ((kl k2).trans
      ((kd k1).trans hdi)))))))
  obtain hbx8 : u8.gpr .ebx = s.gpr .ebx :=
    (k8.gpr _ (by decide)).trans ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans
      ((k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans ((k3.gpr _ (by decide)).trans
        ((k2.gpr _ (by decide)).trans (k1.gpr _ (by decide))))))))
  refine WP.mono (halfEnd_ok u8 hdi8 hbx8) fun v ⟨vdi, vbx, vz, vm, vg, vrd, vwr, vsy⟩ => ?_
  have hst : (halfImpl st).2 = runX xLines (runZ zLines (runX xLines (runZ zLines st))) := rfl
  obtain hks : ws ++ (halfImpl st).1 = ws ++ keys4 aLines (runZ zLines st) ++
      keys4 bLines (runX xLines (runZ zLines st)) ++ keys4 cLines (runZ zLines (runX xLines (runZ zLines st))) ++
      keys4 dLines (runX xLines (runZ zLines (runX xLines (runZ zLines st)))) := by
    simp only [halfImpl, List.append_assoc]
  rw [hst, hks]
  refine ⟨h8.step (vg _ (by decide) (by decide)) (vg _ (by decide) (by decide)) vwr (by rw [vm]; exact h8.xz)
      (by rw [vm]; exact h8.keys) h8.len (by rw [vm]; exact Frame.refl _ _), by rw [vm]; exact E8, ?_, vbx, vz,
    by rw [vsy, s8, s7, s6, s5, s4, s3, s2, s1], fun r hr => ?_, vrd.trans k18.rd, vwr.trans k18.wr⟩
  · rw [vdi, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]
  · have hr' := hr
    simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [vg r hr'.2.2.2.1 hr'.2.2.2.2, k18.gpr r hr]

end

/-! ## The function -/

open VG.Proof.Cast5.X86 (CInv zeroMem zeroMem_cinv copyStep_ok keySavedL keySaved_eq keyRestore_eq keySave_eq
  keySaved_fits keySaved_contains keySaved_in one32 addr_shift)

/-- The facts of key expansion's precondition: the arguments (`key`,
`key_len`, `schedule` and the working space, of 848 bytes) on the stack,
readable; the schedule and the working space writable, apart from the key,
each other, the arguments, the return address and the eight bytes below
`esp`. -/
structure KPreK (s : State) : Prop where
  rdEq : s.rd = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩]
  wrEq : s.wr = [⟨(arg s 2).setWidth 64, 128⟩, ⟨(arg s 3).setWidth 64, 848⟩]
  sp : 8 ≤ (s.gpr .esp).toNat
  spfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  fitk : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  fitK : (arg s 2).toNat + 128 ≤ 2 ^ 32
  fitS : (arg s 3).toNat + 848 ≤ 2 ^ 32
  dkK : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dkS : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 3).setWidth 64, 848⟩
  dKS : Region.Disjoint ⟨(arg s 2).setWidth 64, 128⟩ ⟨(arg s 3).setWidth 64, 848⟩
  dAK : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dAS : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 848⟩
  dRK : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dRS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 848⟩
  dK : Region.Disjoint ⟨(arg s 2).setWidth 64, 128⟩ (below (s.gpr .esp) 8)
  dS : Region.Disjoint ⟨(arg s 3).setWidth 64, 848⟩ (below (s.gpr .esp) 8)
  len : 5 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 16

/-- Key expansion's contract with the working space as the fourth argument,
as its proof states it. -/
def keyY : Contract isa where
  pre s := KPreK s
  post s s' := Spec.Cast5.scheduleAt s'.mem ((arg s 2).setWidth 64) =
    Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

theorem argY_in {s : State} (h : KPreK s) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  obtain hA : InRegions (s.rd ++ s.wr) (argAddr s 0) 16 := by
    rw [h.rdEq]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := h.spfit; omega)
  rw [e0] at hA
  rw [addr_eq (by have := h.spfit; omega), ← Offset.add_add]
  exact CallLay.inRegions_sub hA (by omega) (by decide)

/-- **Key expansion over any look-ups**: the schedule of the key, with the
callee-saved registers and the return address as they were. -/
theorem expandKeyWith_wp {lk : Prog isa} (hlk : KeyLk lk) (s : State) (h : KPreK s) :
    WP isa (expandKeyWith lk) s fun s' => abiPreserved s s' ∧ keyY.post s s' := by
  obtain ⟨kk, hkk⟩ : ∃ x, arg s 0 = x := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ x, arg s 1 = x := ⟨_, rfl⟩
  obtain ⟨K32, hK32⟩ : ∃ x, arg s 2 = x := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ x, arg s 3 = x := ⟨_, rfl⟩
  obtain fitW : S.toNat + 848 ≤ 2 ^ 32 := hS ▸ h.fitS
  obtain fitS : S.toNat + 256 ≤ 2 ^ 32 := by omega
  obtain fitK : K32.toNat + 128 ≤ 2 ^ 32 := hK32 ▸ h.fitK
  obtain fitk : kk.toNat + L.toNat ≤ 2 ^ 32 := hkk ▸ hL ▸ h.fitk
  obtain hlen : 5 ≤ L.toNat ∧ L.toNat ≤ 16 := hL ▸ h.len
  obtain wW : InRegions s.wr (S.setWidth 64) 848 := by rw [h.wrEq, hS]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain wS : InRegions s.wr (S.setWidth 64) 256 := by
    have := CallLay.inRegions_sub wW (off := 0) (l := 256) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  obtain wK : InRegions s.wr (K32.setWidth 64) 128 := by
    rw [h.wrEq, hK32]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain rk : InRegions (s.rd ++ s.wr) (kk.setWidth 64) L.toNat := by
    rw [h.rdEq, hkk, hL]; exact ⟨_, by simp, Region.contains_self _ _⟩
  obtain a0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := argY_in h (i := 0) (by decide)
  obtain a1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := argY_in h (i := 1) (by decide)
  obtain a2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := argY_in h (i := 2) (by decide)
  obtain a3 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4 := argY_in h (i := 3) (by decide)
  have v3 : s.mem.readW (addr (s.gpr .esp) 16) 32 = S := hS
  -- The working space's first 256 bytes, within it.
  obtain sub256 : Region.Sub ⟨S.setWidth 64, 256⟩ ⟨S.setWidth 64, 848⟩ := Region.sub_prefix (by decide)
  obtain dAS : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨S.setWidth 64, 256⟩ := by
    have := h.dAS; rw [hS] at this; exact this.sub_right sub256
  obtain dRS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨S.setWidth 64, 848⟩ := by
    have := h.dRS; rw [hS] at this; exact this
  obtain dkS : Region.Disjoint ⟨kk.setWidth 64, L.toNat⟩ ⟨S.setWidth 64, 848⟩ := by
    have := h.dkS; rw [hkk, hL, hS] at this; exact this
  obtain dSK : Region.Disjoint ⟨K32.setWidth 64, 128⟩ ⟨S.setWidth 64, 848⟩ := by rw [← hK32, ← hS]; exact h.dKS
  obtain dSb : Region.Disjoint ⟨S.setWidth 64, 848⟩ (below (s.gpr .esp) 8) := by rw [← hS]; exact h.dS
  -- The saved registers' memory.
  let g := (s.setReg .eax S).gpr
  let SM := Spill.saveMem s.mem (addr S) g keySaved
  obtain fSM : Frame [⟨S.setWidth 64, 256⟩] s.mem SM :=
    Spill.saveMem_frame List.mem_cons_self (addr S) g keySaved s.mem (keySaved_in fitS)
  have argSM (i : Nat) (hi : i < 3) : SM.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := by
    refine Spill.saveMem_readW_of_sep _ _ (by decide) keySaved s.mem fun p hp => ?_
    refine Region.Disjoint.sep dAS ?_ ?_
    · have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := h.spfit; omega)
      rw [addr_eq (by have := h.spfit; omega), e0, ← Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    · exact keySaved_in fitS p hp
  obtain sk : SM.readW (addr (s.gpr .esp) 4) 32 = kk := (argSM 0 (by decide)).trans hkk
  obtain sl : SM.readW (addr (s.gpr .esp) 8) 32 = L := (argSM 1 (by decide)).trans hL
  obtain sK : SM.readW (addr (s.gpr .esp) 12) 32 = K32 := (argSM 2 (by decide)).trans hK32
  obtain w16 := slot_wr (s := s) fitS wS (d := xOff) (n := 4) (by decide)
  obtain w20 := slot_wr (s := s) fitS wS (d := xOff + 4) (n := 4) (by decide)
  obtain w24 := slot_wr (s := s) fitS wS (d := xOff + 8) (n := 4) (by decide)
  obtain w28 := slot_wr (s := s) fitS wS (d := xOff + 12) (n := 4) (by decide)
  unfold expandKeyWith
  rw [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain h1 : WP isa (.block [.mov .eax (.mem (at_ .esp 16))]) s fun s₁ => s₁ = s.setReg .eax S := by
    crun [a3, v3]
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [keySave_eq]
  refine Spill.save_ok keySaved (fun p hp => ?_) fun s₂ u₂ => ?_
  · rw [wr_setReg, gpr_setReg_self]
    exact slot_wr fitS wS (d := p.2) (n := 4) (by have := keySaved_fits.1 p hp; omega)
  have g₂ : s₂.gpr = g := u₂.gpr
  obtain m₂ : s₂.mem = SM := by rw [u₂.mem]; rfl
  have rd₂ : s₂.rd = s.rd := u₂.rd
  have wr₂ : s₂.wr = s.wr := u₂.wr
  have sy₂ : s₂.syms = s.syms := u₂.syms
  obtain hge : g .eax = S := gpr_setReg_self _ _ _
  obtain hgsp : g .esp = s.gpr .esp := gpr_setReg_of_ne _ _ (by decide)
  obtain hsetup : WP isa (.block keySetup) s₂ fun s₃ => s₃.mem = zeroMem SM S ∧ s₃.gpr .esi = S ∧
      s₃.gpr .edi = kk ∧ s₃.gpr .ebx = L ∧ s₃.gpr .edx = K32 ∧ s₃.gpr .eax = S + BitVec.ofNat 32 16 ∧
      s₃.gpr .esp = s.gpr .esp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧ s₃.syms = s.syms := by
    unfold keySetup
    crun [g₂, m₂, rd₂, wr₂, sy₂, hge, hgsp, a0, a1, a2, sk, sl, sK, w16, w20, w24, w28]
    exact ⟨rfl, rfl⟩
  refine WP.mono hsetup fun s₃ ⟨m₃, si₃, di₃, bx₃, dx₃, ax₃, sp₃, rd₃, wr₃, sy₃⟩ => ?_
  obtain dkS64 : Region.Disjoint ⟨kk.setWidth 64, L.toNat⟩ ⟨S.setWidth 64, 64⟩ :=
    dkS.sub_right (Region.sub_prefix (by decide))
  have hkb (j : Nat) (hj : j < L.toNat) (m : Mem) (hf : Frame [⟨S.setWidth 64, 64⟩] SM m) :
      m (kk.setWidth 64 + BitVec.ofNat 64 j) = SM (kk.setWidth 64 + BitVec.ofNat 64 j) := by
    refine hf.bytes (R := ⟨kk.setWidth 64, L.toNat⟩) (fun r hr => ?_) (by show L.toNat ≤ 2 ^ 64; omega) hj
    rw [List.mem_singleton] at hr; rw [hr]; exact dkS64
  refine WP.seq (wp_countdown (cnt := .ebx) (N := L.toNat) (by omega) (by omega)
    (fun j u => CInv SM (kk.setWidth 64) (S.setWidth 64) j u.mem ∧ u.gpr .edi = kk + BitVec.ofNat 32 j ∧
      u.gpr .eax = S + BitVec.ofNat 32 (16 + j) ∧
      (∀ r, r ∉ [Reg.eax, .edi, .ebx, .ecx] → u.gpr r = s₃.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms)
    (fun j hj u ⟨cu, du, au, gu, rdu, wru, syu⟩ _ => WP.mono (copyStep_ok u (by omega) cu du au
      (by rw [addr_shift]; exact addr_eq (by omega))
      (by rw [addr_shift]; exact addr_eq (by omega))
      (by rw [rdu, wru]; exact CallLay.inRegions_sub rk (by omega) (by omega))
      (by rw [wru]; exact CallLay.inRegions_sub wS (by omega) (by decide))
      (hkb j hj u.mem cu.fr))
      fun v ⟨cv, dv, av, sv, zv, gv, rdv, wrv, syv⟩ => ⟨⟨cv, by rw [dv, one32, add_ofNat_add32 _ j 1], by
        rw [av, one32, add_ofNat_add32 _ (16 + j) 1, Nat.add_assoc], fun r hr => ?keepStep, rdv.trans rdu, wrv.trans wru,
        syv.trans syu⟩, sv, zv⟩)
    (fun u hu => ?rest)
    ⟨by rw [m₃]; exact zeroMem_cinv SM fitS _, by rw [di₃]; exact (BitVec.add_zero _).symm, by rw [ax₃],
      fun _ _ => rfl, rd₃, wr₃, sy₃⟩ (by rw [bx₃, ofNat_toNat32]))
  case keepStep =>
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [gv r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, gu r hr]
  case rest =>
    obtain ⟨cu, -, -, gu, rdu, wru, syu⟩ := hu
    obtain hsi_u : u.gpr .esi = S := (gu .esi (by decide)).trans si₃
    obtain hdx_u : u.gpr .edx = K32 := (gu .edx (by decide)).trans dx₃
    obtain hsp_u : u.gpr .esp = s.gpr .esp := (gu .esp (by decide)).trans sp₃
    refine WP.seq (WP.mono (show WP isa (.block [.mov .edi (.reg .edx), .mov .ebx (imm 2)]) u fun v =>
        v.gpr .edi = K32 ∧ v.gpr .ebx = BitVec.ofNat 32 2 ∧ v.mem = u.mem ∧
          (∀ r, r ≠ .edi → r ≠ .ebx → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms by
      crun [hdx_u]
      exact fun r h1 h2 => by simp only [h1, h2, ite_false]) fun u1 ⟨di1, bx1, m1, g1, rd1, wr1, sy1⟩ => ?_)
    obtain si1 : u1.gpr .esi = S := (g1 .esi (by decide) (by decide)).trans hsi_u
    obtain sp1 : u1.gpr .esp = s.gpr .esp := (g1 .esp (by decide) (by decide)).trans hsp_u
    obtain rd1' : u1.rd = s.rd := rd1.trans rdu
    obtain wr1' : u1.wr = s.wr := wr1.trans wru
    obtain sy1' : u1.syms = s.syms := sy1.trans syu
    -- The memory so far: only the working space's first 256 bytes written.
    obtain fU : Frame [⟨S.setWidth 64, 256⟩] s.mem u1.mem := by
      rw [m1]
      exact fSM.trans (cu.fr.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩)
    -- The arrays after the copy.
    let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem (kk.setWidth 64) L.toNat).getD j 0,
      fun j => u1.mem (S.setWidth 64 + BitVec.ofNat 64 (32 + j))⟩
    obtain xz0 : HoldsXZ u1.mem (S.setWidth 64) st0 := by
      intro a i hi
      cases a with
      | x =>
        rw [show off .x + i = 16 + i from rfl, m1, cu.x i hi]
        show _ = (Spec.Cast5.bytesAt s.mem (kk.setWidth 64) L.toNat).getD i 0
        rw [bytesAt_getD]
        split
        · rw [fSM.bytes (R := ⟨kk.setWidth 64, L.toNat⟩) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact dkS.sub_right sub256)
            (by show L.toNat ≤ 2 ^ 64; omega) (by assumption)]
        · rfl
      | z => rfl
    obtain ks0 : KE u1.mem S (K32.setWidth 64) u1 st0 [] :=
      ⟨si1, fitW, by rw [wr1']; exact wW, xz0, fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _,
        Nat.zero_le _, by rw [wr1']; exact wK, dSK, by rw [sp1]; exact h.sp, by rw [sp1]; exact dSb,
        by rw [sp1, ← hK32]; exact h.dK⟩
    -- The look-ups of `x`.
    refine WP.seq (WP.mono (look_ok hlk ks0 .x) fun u2 ⟨ks2, E2, _, sy2, k2⟩ => ?_)
    refine WP.seq (wp_countdown (cnt := .ebx) (N := 2) (by decide) (by decide)
      (fun hh v => KE u1.mem S (K32.setWidth 64) v (halves st0 hh).1 (halves st0 hh).2 ∧
        Entries v.mem S (halves st0 hh).1.x ∧
        v.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh) ∧ v.syms = s.syms ∧ Keep halfRegs u1 v)
      (fun hh hh2 v ⟨kv, ev, dv, syv, kpv⟩ _ => WP.mono (halfK_ok hlk kv ev rfl fitK dv (halves_length st0 hh) hh2)
        fun w ⟨kw, ew, dw, sw, zw, syw, kpw⟩ => ⟨⟨kw, ew, dw, syw.trans syv, kpv.trans kpw⟩, sw, zw⟩)
      (fun v hv => ?fin)
      ⟨ks2, E2, by rw [k2.gpr _ (by decide), di1]; exact (BitVec.add_zero _).symm, sy2.trans sy1', keepH k2⟩
      ((k2.gpr _ (by decide)).trans bx1))
    case fin =>
      obtain ⟨kv, -, -, syv, kpv⟩ := hv
      obtain vsi : v.gpr .esi = S := (kpv.gpr .esi (by decide)).trans si1
      obtain vsp : v.gpr .esp = s.gpr .esp := (kpv.gpr .esp (by decide)).trans sp1
      obtain vrd : v.rd = s.rd := kpv.rd.trans rd1'
      obtain vwr : v.wr = s.wr := kpv.wr.trans wr1'
      -- The saved registers.
      obtain hs0 : Spill.Saved SM (addr S) g keySaved := Spill.saveMem_saved_addr s.mem g keySaved_fits fitS
      obtain d64 : Region.Disjoint (slotR S 64 16) ⟨S.setWidth 64, 64⟩ :=
        Offset.disjoint_base _ (by decide) (by decide)
      obtain hs1 : Spill.Saved u1.mem (addr S) g keySaved := by
        rw [m1]
        exact hs0.of_frame cu.fr (keySaved_contains fitS) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact d64
      obtain sv64 : Region.Sub (slotR S 64 16) ⟨S.setWidth 64, 848⟩ := Offset.sub_base _ (by decide)
      obtain hs2 : Spill.Saved v.mem (addr S) g keySaved := by
        refine hs1.of_frame kv.fr (keySaved_contains fitS) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact d64
        · exact (dSK.symm).sub_left sv64
        · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
        · rw [vsp]; exact dSb.sub_left sv64
      rw [keyRestore_eq, keySaved_eq, ← List.append_nil (Spill.restoreCode _ _)]
      refine Spill.restoreBase_ok keySavedL (by decide) (fun p hp => ?_) (by rw [vsi, ← keySaved_eq]; exact hs2)
        fun s' hr => WP.block_nil ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
      · rw [vsi, vrd, vwr]
        rw [← keySaved_eq] at hp
        exact slot_rd fitS wS (d := p.2) (n := 4) (by have := keySaved_fits.1 p hp; omega)
      · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl
        · exact (hr.gpr (.ebx, keySavedOff) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.esi, keySavedOff + 4) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.edi, keySavedOff + 8) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.ebp, keySavedOff + 12) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.other .esp (by decide)).trans vsp
      · have dR : ∀ r ∈ ([loR S, ⟨K32.setWidth 64, 128⟩, lkR S, below (v.gpr .esp) 8] : List Region),
            Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r := by
          intro r hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl | rfl | rfl
          · exact dRS.sub_right (Region.sub_prefix (by decide))
          · rw [← hK32]; exact h.dRK
          · exact dRS.sub_right (lk_sub S)
          · rw [vsp, below, Taint.sub_setWidth h.sp]
            exact Offset.base_disjoint_below _ (by decide)
        rw [hr.mem, kv.fr.readW (Region.contains_self _ _) dR (by decide),
          fU.readW (Region.contains_self _ _) (fun r hr' => by
            rw [List.mem_singleton] at hr'; subst hr'; exact dRS.sub_right sub256) (by decide)]
      · show Spec.Cast5.scheduleAt s'.mem _ = _
        rw [hr.mem, hK32, hkk, hL, scheduleAt_keys kv.keys (halves_length st0 2),
          Proof.Cast5.expandKey_eq _ st0.z, halves_two]

/-! ## The look-ups' function

What follows is about `lookup`'s code: the registers its instructions use,
an instruction at a time, by the lemmas of the one-block look-ups
(`Ssse3Lookup.lean`: the index vectors, the planes' rows) and of the
sixteen blocks' (`Ssse3WideCore.lean`: the planes' bytes to doublewords). -/

open VG.Impl.Cast5.X86.Ssse3 (tb x stx tbr tableName oM oT oC vOff index sboxOf)
open VG.Impl.Cast5.X86.Ssse3.Wide (entries transpose enOff)
open VG.Proof.Cast5.X86.Ssse3.Wide (transpose4_wp en_dword rd_wr)

/-- The high nibbles of the bytes of `X`. -/
abbrev hiN (X : BitVec 128) : BitVec 128 := XBinOp.eval .pand (XShiftOp.eval .psrld X 4) (cst oM)
/-- The low nibbles. -/
abbrev loN (X : BitVec 128) : BitVec 128 := XBinOp.eval .pand X (cst oM)

theorem sboxK_eq (j : Nat) (is : List Instr) : Impl.Cast5.X86.Ssse3.Key.sbox j ++ is =
    Impl.Cast5.X86.Ssse3.scan (4 + j) ++ (transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm0 .xmm1 .xmm2 .xmm3 ++ (tb .xmm5 oT ::
      x .pshufb .xmm4 .xmm5 :: x .pshufb .xmm2 .xmm5 :: x .pshufb .xmm0 .xmm5 :: x .pshufb .xmm3 .xmm5 ::
      stx .esi (enOff j 0) .xmm4 :: stx .esi (enOff j 1) .xmm2 :: stx .esi (enOff j 2) .xmm0 ::
      stx .esi (enOff j 3) .xmm3 :: is)) := by
  rw [Impl.Cast5.X86.Ssse3.Key.sbox, entries]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- A store of the look-ups, in their part of the working space. -/
theorem lk_contains (W : BitVec 32) {o : Nat} (h : 272 ≤ o) (h' : o + 16 ≤ 848) :
    (lkR W).Contains (slot W o) (128 / 8) := Offset.contains _ h (by omega) (by decide)

variable {s : State} {m : Mem}

/-- **An S-box at the sixteen bytes**: with the index vectors of the bytes of
`X` in the working space, `S_{5+j}`'s entries at them, four a place, with
those of the S-boxes before it. -/
theorem sboxK_wp {W : BitVec 32} (E : Env W s) (fW : W.toNat + 848 ≤ 2 ^ 32)
    (wrE : ∀ o n, 272 ≤ o → o + n ≤ 848 → InRegions s.wr (slot W o) n) {X : BitVec 128} {m₀ : Mem}
    {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {j : Nat} (hj : j < 4)
    (hV : ∀ r < 16, vAt m W r = ByteLookup.idx (cst (oC r)) (hiN X) (loN X)) (hf : Frame [lkR W] m₀ m)
    (hF : ∀ j' < j, ∀ gI < 4, ∀ c < 4,
      dword (m.readW (slot W (enOff j' gI)) 128) c = sboxOf (4 + j') (byte X (4 * gI + c)))
    (k : ∀ m' g, (∀ r < 16, vAt m' W r = ByteLookup.idx (cst (oC r)) (hiN X) (loN X)) → Frame [lkR W] m₀ m' →
      (∀ j' < j + 1, ∀ gI < 4, ∀ c < 4,
        dword (m'.readW (slot W (enOff j' gI)) 128) c = sboxOf (4 + j') (byte X (4 * gI + c))) →
      WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (Impl.Cast5.X86.Ssse3.Key.sbox j ++ is)) (S s m f) Q := by
  have st (o : Nat) (h : 592 ≤ o) (h' : o + 16 ≤ 848) {m1 : Mem} {g : XReg → BitVec 128} {r : XReg}
      {is' : List Instr} (k' : WP isa (.block is') (S s (m1.writeW (slot W o) (g r)) g) Q) :
      WP isa (.block (stx .esi o r :: is')) (S s m1 g) Q :=
    wp_st (ea_at E.esi (by omega)) (wrE _ _ (by omega) h') k'
  rw [sboxK_eq]
  refine scan_wp E (by omega) fun f2 hA => transpose4_wp fun f3 r0 r1 r2 r3 => wp_tb E.edx (by decide)
    (wp_bin (wp_bin (wp_bin (wp_bin (st _ (by simp only [enOff]; omega) (by simp only [enOff]; omega)
      (st _ (by simp only [enOff]; omega) (by simp only [enOff]; omega)
      (st _ (by simp only [enOff]; omega) (by simp only [enOff]; omega)
      (st _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) ?_))))))))
  have a4 : f2 .xmm4 = _ := hA 0 (by decide)
  have a5 : f2 .xmm5 = _ := hA 1 (by decide)
  have a6 : f2 .xmm6 = _ := hA 2 (by decide)
  have a7 : f2 .xmm7 = _ := hA 3 (by decide)
  rw [a4, a5, a6, a7] at r0 r1 r2 r3
  simp only [upd, reduceCtorEq, ↓reduceIte, r0, r1, r2, r3]
  have me : lkR W ∈ [lkR W] := List.mem_cons_self
  have hc (g : Nat) (hg : g < 4) : (lkR W).Contains (slot W (enOff j g)) (128 / 8) :=
    lk_contains W (by simp only [enOff]; omega) (by simp only [enOff]; omega)
  have ed (gI c : Nat) (hgI : gI < 4) (hc' : c < 4) := en_dword (m1 := m) (W := W) (t := fun i => byte X i)
    (IO := X) (j := 4 + j) (gI := gI) (c := c) (by omega) hgI hc' (fun _ _ => rfl) hV
  refine k _ _ (fun r hr => ?_) ((((hf.writeW me _ (hc 0 (by decide))).writeW me _ (hc 1 (by decide))).writeW me _
    (hc 2 (by decide))).writeW me _ (hc 3 (by decide))) fun j' hj' gI hgI c hc' => ?_
  · show Mem.readW _ (slot W (vOff r)) 128 = _
    rw [rd_wr _ W _ (by simp only [vOff, enOff]; omega) (by simp only [vOff]; omega) (by simp only [enOff]; omega),
      rd_wr _ W _ (by simp only [vOff, enOff]; omega) (by simp only [vOff]; omega) (by simp only [enOff]; omega),
      rd_wr _ W _ (by simp only [vOff, enOff]; omega) (by simp only [vOff]; omega) (by simp only [enOff]; omega),
      rd_wr _ W _ (by simp only [vOff, enOff]; omega) (by simp only [vOff]; omega) (by simp only [enOff]; omega)]
    exact hV r hr
  · by_cases e : j' = j
    · subst e
      rcases cases4 hgI with rfl | rfl | rfl | rfl
      · rw [rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
          rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
          rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
          readW_self128]
        exact ed 0 c (by decide) hc'
      · rw [rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
          rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
          readW_self128]
        exact ed 1 c (by decide) hc'
      · rw [rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
          readW_self128]
        exact ed 2 c (by decide) hc'
      · rw [readW_self128]
        exact ed 3 c (by decide) hc'
    · rw [rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
        rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
        rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
        rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega)]
      exact hF j' (by omega) gI hgI c hc'

open VG.X86.Wp

theorem lookup_eq : lookup = .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.block (.mov tbr (.reg .eax) :: tb .xmm2 oM :: x .movdqa .xmm1 .xmm0 :: .xop (.shift .psrld .xmm1 4) ::
      x .pand .xmm1 .xmm2 :: x .pand .xmm0 .xmm2 :: ((List.range' 0 16).flatMap index ++
        (Impl.Cast5.X86.Ssse3.Key.sbox 0 ++ (Impl.Cast5.X86.Ssse3.Key.sbox 1 ++
          (Impl.Cast5.X86.Ssse3.Key.sbox 2 ++ (Impl.Cast5.X86.Ssse3.Key.sbox 3 ++ []))))))) := by
  rw [lookup, Impl.Cast5.X86.Ssse3.Key.nibbles, List.range_eq_range']
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

/-- The S-boxes of key expansion are those of the table from the fifth on. -/
theorem sboxOf_key : ∀ j < 4, sboxOf (4 + j) = Proof.Cast5.sbox (5 + j) := by
  intro j hj
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

/-- **The look-ups' function**: S5 to S8 at the sixteen bytes of `xmm0`, in
the working space; it writes the working space's bytes 272 to 847 and the
four bytes below `esp`. -/
theorem lookup_wp {s : State} {W : BitVec 32} (hW : s.gpr .esi = W) (fW : W.toNat + 848 ≤ 2 ^ 32)
    (wrW : ∀ o n, 272 ≤ o → o + n ≤ 848 → InRegions s.wr (slot W o) n) (hsp : 4 ≤ (s.gpr .esp).toNat) :
    WP isa lookup s fun t => Entries t.mem W (fun i => byte (s.xmm .xmm0) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms ∧ Frame [lkR W, below (s.gpr .esp) 4] s.mem t.mem := by
  rw [lookup_eq]
  refine WP.seq (WP.mono (symFrame_ok' tableName s hsp) fun s₀ ⟨h₀, x₀⟩ => ?_)
  refine Wp.cons (s' := s₀.setReg tbr (s₀.gpr .eax)) rfl ?_
  obtain u₁ := Upd.setReg s₀ tbr (s₀.gpr .eax)
  obtain x₁ : (s₀.setReg tbr (s₀.gpr .eax)).xmm = s₀.xmm := xmm_setReg _ _ _
  generalize s₀.setReg tbr (s₀.gpr .eax) = s₁ at u₁ x₁ ⊢
  obtain E : Env W s₁ := ⟨(u₁.other _ (by decide)).trans ((h₀.gpr _ (by decide)).trans hW),
    by rw [u₁.gpr, h₀.addr, u₁.syms, h₀.syms], by omega, by
      rw [u₁.wr, h₀.wr]; exact fun o n h h' => wrW o n h (by omega)⟩
  have wrE : ∀ o n, 272 ≤ o → o + n ≤ 848 → InRegions s₁.wr (slot W o) n := by rw [u₁.wr, h₀.wr]; exact wrW
  obtain ⟨X, hX⟩ : ∃ X, s.xmm .xmm0 = X := ⟨_, rfl⟩
  have hx1 : s₁.xmm .xmm0 = X := by rw [x₁, x₀]; exact hX
  show WP isa _ (S s₁ s₁.mem s₁.xmm) _
  refine wp_tb E.edx (by decide) (wp_bin (wp_xs rfl (wp_bin (wp_bin (indexes_wp E (m₀ := s₁.mem) (H := hiN X)
    (L := loN X) 16 0 s₁.mem _ (by decide) (by simp only [upd, reduceCtorEq, ↓reduceIte, hx1])
    (by simp only [upd, reduceCtorEq, ↓reduceIte, hx1]; rfl) (fun r' hr' => absurd hr' (Nat.not_lt_zero _))
    (Frame.refl _ _) fun m1 g1 hV1 hf1 =>
    sboxK_wp E fW wrE (by decide) hV1 (hf1.sub fun r hr => ⟨_, List.mem_cons_self, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
      (fun j' hj' => absurd hj' (Nat.not_lt_zero _)) fun m2 g2 hV2 hf2 hF2 =>
    sboxK_wp E fW wrE (by decide) hV2 hf2 hF2 fun m3 g3 hV3 hf3 hF3 =>
    sboxK_wp E fW wrE (by decide) hV3 hf3 hF3 fun m4 g4 hV4 hf4 hF4 =>
    sboxK_wp E fW wrE (by decide) hV4 hf4 hF4 fun m5 g5 _ hf5 hF5 =>
    WP.block_nil ⟨fun e h5 h8 i hi => ?_, fun r a b c => ?_, u₁.rd.trans h₀.rd, u₁.wr.trans h₀.wr,
      u₁.syms.trans h₀.syms, ?_⟩)))))
  · obtain ⟨j, rfl⟩ : ∃ j, e = 5 + j := ⟨e - 5, by omega⟩
    have hj : j < 4 := by omega
    have := hF5 j hj (i / 4) (by omega) (i % 4) (Nat.mod_lt _ (by decide))
    rw [dword_readW _ _ (Nat.mod_lt _ (by decide)), Offset.add_add, show 4 * (i / 4) + i % 4 = i by omega,
      sboxOf_key j hj] at this
    show m5.readW (slot W (enAt (5 + j) i)) 32 = Proof.Cast5.sbox (5 + j) (byte (s.xmm .xmm0) i)
    rw [hX, ← this]
    exact congrArg (fun o => m5.readW (slot W o) 32) (by simp only [enAt, enOff]; omega)
  · exact (u₁.other r c).trans (h₀.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a, b⟩))
  · refine (h₀.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
    rw [← u₁.mem]
    exact hf5.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self

/-- **The call of the look-ups' function**, with eight bytes of stack apart
from the working space. -/
theorem call_wp {s : State} {W : BitVec 32} (hW : s.gpr .esi = W) (fW : W.toNat + 848 ≤ 2 ^ 32)
    (wrW : ∀ o n, 272 ≤ o → o + n ≤ 848 → InRegions s.wr (slot W o) n) (hsp : 8 ≤ (s.gpr .esp).toNat)
    (dWS : Region.Disjoint (lkR W) (below (s.gpr .esp) 8)) :
    WP isa (.call lookName lookup) s fun t => Entries t.mem W (fun i => byte (s.xmm .xmm0) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms ∧ Frame [lkR W, below (s.gpr .esp) 8] s.mem t.mem := by
  obtain ⟨r4, r8, d48⟩ := call_regions hsp
  obtain cm : s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := State.callEntry_mem s
  obtain fc : Frame [below (s.gpr .esp) 8] s.mem s.callEntry.mem := by
    rw [cm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_top (by decide) hsp (by decide))
  obtain esp' : s.callEntry.gpr .esp = s.gpr .esp - 4 := State.callEntry_esp s
  refine WP.callBody (WP.mono (lookup_wp (s := s.callEntry) ((State.callEntry_gpr s (by decide)).trans hW) fW wrW
    (by rw [esp', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega)]; omega))
    fun u ⟨hres, hg, hrd, hwr, hsy, hfr⟩ => ⟨?_, ?_, ?_⟩)
  · exact (hg .esp (by decide) (by decide) (by decide)).trans esp'
  · rw [esp'] at hfr
    rw [hfr.readW (r := below (s.gpr .esp) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide), cm]
    · exact Mem.readW_writeW_self32 _ _ _
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact (dWS.sub_right r4).symm
      · rw [List.mem_singleton.mp hr]; exact d48
  · obtain U := Upd.setReg u .esp (s.gpr .esp)
    refine ⟨?_, fun r a b c => ?_, U.rd.trans hrd, U.wr.trans hwr, U.syms.trans hsy, ?_⟩
    · rw [U.mem]; exact hres
    · by_cases h : r = .esp
      · rw [h]; exact U.gpr
      · exact (U.other r h).trans ((hg r a b c).trans (State.callEntry_gpr s h))
    · rw [U.mem]
      refine (fc.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self).trans
        (hfr.sub fun r hr => ?_)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · rw [List.mem_singleton.mp hr, esp']
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, r8⟩

/-- The function's call is what key expansion needs of its look-ups. -/
theorem lookupLk : KeyLk (.call lookName lookup) where
  ok s W hW fW wW hsp dW := call_wp hW fW (fun o n _ h' => CallLay.inRegions_sub wW h' (by decide)) hsp
    (dW.sub_left (lk_sub W))

/-- **Key expansion**, with its working space as the fourth argument. -/
theorem expandKey_wp (s : State) (h : KPreK s) :
    WP isa Impl.Cast5.X86.Ssse3.Key.expandKey s fun s' => abiPreserved s s' ∧ keyY.post s s' :=
  expandKeyWith_wp lookupLk s h

/-! ## Constant time -/

/-- The initial taint: `esp`, the 16 bytes of arguments (the fourth, the base
of writable region 1, the working space) and the 8 bytes of stack below `esp`
outside every writable region. -/
def τK : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128, 848], argLen := 20, argBases := [(16, 1)], room := 8 }

theorem τK_wf {s : State} (h : keyY.pre s) : VG.X86.Taint.Wf τK s := by
  have hw := h.wrEq
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨h.spfit, ?_⟩, ?_⟩ ?_
  · rw [hw]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
      and_true]
    exact ⟨h.dKS, fun _ h => h.elim⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simp only [toNat_setWidth]; exact h.fitK
    · simp only [toNat_setWidth]; exact h.fitS
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := h.spfit; omega) h.dRK h.dAK
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := h.spfit; omega) h.dRS h.dAS
  · intro p hp
    simp only [τK, List.mem_singleton] at hp
    subst hp
    refine ⟨by decide, ?_⟩
    simp only [VG.X86.Taint.region, hw]
    show addr (arg s 3) 0 = _
    rw [addr_off h.fitS 0 (by decide), BitVec.add_zero]
    rfl
  · intro _
    refine ⟨h.sp, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8 = (s.gpr .esp - BitVec.ofNat 32 8).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth h.sp).symm
    simp only [τK]
    rw [e]
    simp only [hw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dK.symm
    · exact h.dS.symm

theorem τK_agree {s₁ s₂ : State} (h₁ : keyY.pre s₁) (h₂ : keyY.pre s₂) (hp : keyY.pub s₁ s₂) :
    VG.X86.Taint.Agree τK s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τK_wf h₁, τK_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τK, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.wrEq, h₂.wrEq, args 2 (by decide), args 3 (by decide)]
  · simp only [τK] at hk
    rw [show VG.X86.Taint.depth τK.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := h₁.spfit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := h₂.spfit; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

/-- Constant time, by the taint analysis of the function with its look-ups'
function at each of its calls: only `esp`, the arguments and the key's
length decide an address or a branch. -/
theorem expandKey_ct : ConstantTime isa keyY.pre keyY.pub Impl.Cast5.X86.Ssse3.Key.expandKey :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) τK (fun _ _ h₁ h₂ hp => τK_agree h₁ h₂ hp) (by taint_decide)

/-! ## The contracts -/

/-- Key expansion's signature without the working space that its `Api`
gives it. -/
def sig3 : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 128)]

/-- `key_len` is from 5 to 16. -/
def pre3 (pb : Nat) : Curry (sig3.words pb) (Mem → Prop) :=
  fun _key keyLen _schedule _ => Spec.Cast5.validKey keyLen.toNat

/-- The subkeys of the `key_len` bytes at `key` are at `schedule`. -/
def post3 (pb : Nat) : sig3.Post pb := fun key keyLen schedule m m' _ =>
  Spec.Cast5.scheduleAt m' schedule = Spec.Cast5.expandKey (Spec.Cast5.bytesAt m key keyLen.toNat)

/-- The function's contract with the working space, 106 64-bit words, as the
fourth argument. -/
abbrev keyScratch : Contract isa :=
  Sig.scratchContract X86.abi sig3 "scratch" .u64 106 (pre3 X86.abi.ptrBits) (post3 X86.abi.ptrBits) false 8

/-- The arguments of the witnesses, at `0x8004`: a key of 16 bytes at
`0x1000`, the schedule at `0x2000` and a working space at `0x4000`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else if a = 0x8011 then 0x40
  else 0

/-- A state with those arguments that may read `rd` and write `wr`. -/
def satS (rd wr : List Region) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satArgs
  rd := rd
  wr := wr
  syms _ := 0

theorem keyY_implies : keyY.Implies keyScratch where
  pre s h := by
    sig_pre [Sig.scratchContract, Sig.withScratch, sig3, pre3, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, stackBelow, Curry.withScratch, Curry.app] at h
    obtain ⟨h8, hsp, hrd, hwr, dkK, dkS, dKS, dKA, dSA, -, dRK, dRS, -, -, dBK, dBS, -, fk, fK, fS, hv⟩ := h
    have be := below8 h8
    exact ⟨hrd, hwr, h8, by omega, fk, fK, fS, dkK, dkS, dKS, dKA.symm, dSA.symm, dRK, dRS,
      by rw [be]; exact dBK.symm, by rw [be]; exact dBS.symm, hv⟩
  post := by
    intro s t _ h
    sig_post [Sig.scratchContract, Sig.withScratch, sig3, post3, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, Curry.withScratch]
    exact h
  pub s t _ _ h := by
    sig_pub [Sig.scratchContract, Sig.withScratch, sig3, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      Curry.withScratch] at h
    obtain ⟨hsp, h0, h1, h2, h3⟩ := h
    refine ⟨hsp, fun i hi => ?_⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  sat := by
    refine ⟨satS [⟨0x1000, 16⟩, ⟨0x8004, 16⟩] [⟨0x2000, 128⟩, ⟨0x4000, 848⟩], ?_⟩
    sig_pre [Sig.scratchContract, Sig.withScratch, sig3, pre3, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, Curry.withScratch, Curry.app, satS, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    sig_and_intros
    all_goals first | rfl | decide | exact ⟨by decide, by decide⟩ | exact Region.disjoint_of_sep (by decide)

theorem expandKey_verified : Verified X86.target Impl.Cast5.X86.Ssse3.Key.expandKey keyScratch :=
  Verified.of_correct (fun s hs => expandKey_wp s hs) expandKey_ct keyY_implies

/-! ## The frame -/

open VG.Proof.Cast5.ScrubLocal

/-- The key's bytes in two memories that agree on them. -/
theorem keyBytes_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : Spec.Cast5.bytesAt m₂ p n = Spec.Cast5.bytesAt m₁ p n := by
  simp only [Spec.Cast5.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have := List.mem_range.mp hi
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

/-- The precondition reads no memory. -/
theorem pre3_local : ∀ vs m₁ m₂, vs.length = (sig3.words X86.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs sig3.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig3.words X86.abi.ptrBits) (pre3 X86.abi.ptrBits) vs m₁ →
      Curry.apply (sig3.words X86.abi.ptrBits) (pre3 X86.abi.ptrBits) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  match vs, hlen with
  | [k, kl, sch], _ => exact h

/-- The postcondition reads the memory on entry only within the key. -/
theorem post3_local : ∀ vs m₁ m₂ m' r, vs.length = (sig3.words X86.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs sig3.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig3.words X86.abi.ptrBits) (post3 X86.abi.ptrBits) vs m₁ m' r →
      Curry.apply (sig3.words X86.abi.ptrBits) (post3 X86.abi.ptrBits) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [k, kl, sch], _ =>
    simp only [sig3, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    show Spec.Cast5.scheduleAt m' sch = Spec.Cast5.expandKey (Spec.Cast5.bytesAt m₂ k _)
    rw [keyBytes_of hb.1 (len1P kl)]
    exact h

/-- The postcondition reads the memory on return only within the schedule. -/
theorem post3Out_local : ∀ vs m m₁ m₂ r, vs.length = (sig3.words X86.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs sig3.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig3.words X86.abi.ptrBits) (post3 X86.abi.ptrBits) vs m m₁ r →
      Curry.apply (sig3.words X86.abi.ptrBits) (post3 X86.abi.ptrBits) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [k, kl, sch], _ =>
    simp only [sig3, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    show Spec.Cast5.scheduleAt m₂ sch = _
    rw [scheduleAt_of hb.2]
    exact h

/-- The contract of the function with its working space in a frame, by the
signature without the caller's: 888 bytes of stack. -/
abbrev keyFrame : Contract isa :=
  sig3.contract X86.abi (pre3 X86.abi.ptrBits) (post3 X86.abi.ptrBits) false 888

theorem frame_sat : ∃ s, keyFrame.pre s := by
  refine ⟨satS [⟨0x1000, 16⟩, ⟨0x8004, 12⟩] [⟨0x2000, 128⟩], ?_⟩
  sig_pre [sig3, pre3, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satS, satArgs, X86.arg, X86.argAddr,
    Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact ⟨by decide, by decide⟩ | exact Region.disjoint_of_sep (by decide)

/-- Key expansion with its working space on the stack, zeroed on return. -/
theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 880 3 212 Impl.Cast5.X86.Ssse3.Key.expandKey)
      keyFrame :=
  X86.Verified.stackScratchWiped (sig := sig3) (nm := "scratch") (e := .u64) (n := 106)
    (pre := pre3 X86.abi.ptrBits) (post := post3 X86.abi.ptrBits) (wa := false) (stack := 8)
    (bytes := 880) expandKey_verified (by decide) (by lit_decide) (by lit_decide)
    (by decide) pre3_local post3_local post3Out_local frame_sat

/-! ## The `Api`'s contract -/

/-- What the function reads, of what its `Api`'s contract lets it: the key
and its first three arguments. -/
def rd3 (s : State) : List Region := [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 12⟩]
/-- What it writes: the schedule, and not the caller's `scratch`. -/
def wr3 (s : State) : List Region := [⟨(arg s 2).setWidth 64, 128⟩]

/-- The `Api`'s precondition gives the frame's, with the regions `rd3` and
`wr3`. -/
theorem api_pre (s : State) (h : (Spec.Cast5.expandKeyContract X86.abi 888).pre s) :
    keyFrame.pre (s.withRegions (rd3 s) (wr3 s)) ∧
      s.rd = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩] ∧
      s.wr = [⟨(arg s 2).setWidth 64, 128⟩, ⟨(arg s 3).setWidth 64, 256⟩] := by
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, stackBelow] at h
  obtain ⟨h9, hsp, hrd, hwr, dkK, -, -, dKA, -, dRk, dRK, -, dRA, dBk, dBK, -, dBA, fk, fK, -, hv⟩ := h
  refine ⟨?_, hrd, hwr⟩
  sig_pre [sig3, pre3, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr, rd3, wr3]
  exact ⟨h9, by omega, dkK, dKA.sub_right (Region.sub_prefix (by decide)), dRk, dRK,
    dRA.sub_right (Region.sub_prefix (by decide)), dBk, dBK, dBA.sub_right (Region.sub_prefix (by decide)), fk, fK,
    hv⟩

theorem api_sat : ∃ s, (Spec.Cast5.expandKeyContract X86.abi 888).pre s := by
  refine ⟨satS [⟨0x1000, 16⟩, ⟨0x8004, 16⟩] [⟨0x2000, 128⟩, ⟨0x4000, 256⟩], ?_⟩
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, satS, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact ⟨by decide, by decide⟩ | exact Region.disjoint_of_sep (by decide)

/-- **Key expansion with the working space in the function's own frame
meets the contract of its `Api`**: it reads the key and its first three
arguments and writes the schedule, so neither reads nor writes the caller's
`scratch`. -/
theorem expandKey_api :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 880 3 212 Impl.Cast5.X86.Ssse3.Key.expandKey)
      (Spec.Cast5.expandKeyContract X86.abi 888) := by
  refine Verified.narrowTo expandKey_framed rd3 wr3 (fun s h => (api_pre s h).1) (fun s h => ?_) (fun s h => ?_)
    (fun s s' _ hp => ?_) (fun s₁ s₂ _ _ hp => ?_) api_sat
  · obtain ⟨-, hrd, hwr⟩ := api_pre s h
    rw [hrd, hwr]
    intro a n ⟨r, hr, hc⟩
    simp only [rd3, wr3, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, hc⟩
    · exact ⟨⟨argAddr s 0, 16⟩, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [Region.Contains] at hc ⊢; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hc⟩
  · obtain ⟨-, -, hwr⟩ := api_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wr3, List.mem_singleton] at hr
    subst hr; exact List.mem_cons_self
  · sig_post [sig3, post3, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.X86.arg_withRegions,
      VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem] at hp
    sig_post [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeyPost, Spec.Cast5.expandKeySig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes]
    exact hp
  · sig_pub [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at hp
    obtain ⟨hsp, h0, h1, h2, -⟩ := hp
    sig_pub [sig3, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.X86.arg_withRegions,
      VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem]
    exact ⟨hsp, h0, h1, h2⟩

/-! ## The function as emitted -/

open VG.X86.Scrub

/-- The postcondition reads the memory on return only within the schedule. -/
theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract X86.abi stack) (Spec.Cast5.expandKeySig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [k, kl, sch, sc], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [scheduleAt_of hb.2.1]
      exact h

/-- `Spec.Cast5.expandKeyApi` as emitted (`Impl.Cast5.X86.Ssse3.Key.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Fn.expandKey (Spec.Cast5.expandKeyContract X86.abi 888) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.expandKeyApi) (W := 888)
    { code := Impl.StackScratch.X86.withStackScratchWiped 880 3 212 Impl.Cast5.X86.Ssse3.Key.expandKey
      verified := expandKey_api }
    Fn.words (expandKeyOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Cast5.X86.Ssse3.Key
