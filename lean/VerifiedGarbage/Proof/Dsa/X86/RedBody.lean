module

public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Dsa.X86.Arith
import VerifiedGarbage.Proof.Dsa.X86.MulBody
import VerifiedGarbage.Proof.Dsa.X86.Stream
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # IA-32 DSA reductions with their callee-saved registers restored -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (Entry save_ok restore_ok)
open VG.Proof.Dsa.X86 (StreamInput LenSrc streamRanges setupRanges_whole streamRanges_whole reduceStream_ok)

/-- A word apart from the working space keeps its value across changes within it. -/
theorem readW_apart {base : Addr} {o n size : Nat} {m m' : Mem} {a : Addr} (h : Outside base o n m m')
    (ho : o + n ≤ size) (hd : Region.Disjoint ⟨a, 4⟩ ⟨base, size⟩) : m'.readW a 32 = m.readW a 32 :=
  (Mem.readW_congr fun i hi => (h _ (.inr (by
    have := hd _ (Offset.contains_base a (d := i) (n := 1) (k := 4) (by omega) (by omega))
    simp only [Region.Contains] at this
    simp only [ofs]
    omega))).symm).symm

/-- What a reduction needs of the state it starts in, besides the modulus:
its stack arguments readable and apart from the working space, the bytes'
address `p` and length `len`, and the bytes readable and apart from the
context. -/
structure In (n : Nat) (s : State) (base : Addr) (size : Nat) (p : BitVec 32) (len : Nat) : Prop where
  entry : Entry s base size
  arg2 : InRegions (s.rd ++ s.wr) (argAddr s 2) 4
  arg3 : InRegions (s.rd ++ s.wr) (argAddr s 3) 4
  apart2 : Region.Disjoint ⟨argAddr s 2, 4⟩ ⟨base, size⟩
  apart3 : Region.Disjoint ⟨argAddr s 3, 4⟩ ⟨base, size⟩
  data : arg s 2 = p
  length : arg s 3 = BitVec.ofNat 32 len
  lenFit : len < 2 ^ 32
  input : StreamInput s base (contextBytes n) p len

/-- What the prefix leaves for the stream: the context, the bytes' address in
`esi` and their length in the header, the saved registers, and changes only
within the header and the context. -/
structure Ready (n m : Nat) (s x : State) (base : Addr) (size : Nat) (p : BitVec 32) (len : Nat) : Prop where
  ctx : Context n m base size x
  esi : x.gpr .esi = p
  lenSrc : LenSrc base size n x (.mem (sc lenAt)) len
  input : StreamInput x base (contextBytes n) p len
  outs : Outs base (scratch n) s.mem x.mem
  outside : Outside base 0 (contextBytes n) s.mem x.mem
  saved : Saved x.mem (off base) s.gpr slots
  esp : x.gpr .esp = s.gpr .esp
  rd : x.rd = s.rd
  wr : x.wr = s.wr

theorem prefix_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32}
    (I : In n s base size p len) (hz : contextBytes n ≤ size) (hn : 0 < n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm : 255 < m) (hodd : m % 2 = 1) :
    WP isa (reducePrefix n) s fun x => Ready n m s x base size p len := by
  have E := I.entry
  have nw := E.nowrap
  have hz' := hz
  simp only [contextBytes, slot, stride] at hz'
  have hz24 : 24 ≤ size := by omega
  unfold reducePrefix
  refine WP.seq (WP.mono (save_ok E hz24) fun u ⟨Su, Sv, Ou, Ku⟩ => ?_)
  have usp : u.gpr .esp = s.gpr .esp := Ku.1 _ (by decide)
  -- the arguments, as the saves left them
  have a3 : u.mem.readW (addr (u.gpr .esp) 16) 32 = BitVec.ofNat 32 len := by
    rw [usp]
    exact (readW_apart Ou (by omega) I.apart3).trans I.length
  have a2 : u.mem.readW (addr (u.gpr .esp) 12) 32 = p := by
    rw [usp]
    exact (readW_apart Ou (by omega) I.apart2).trans I.data
  have r3 : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 16) 4 := by
    rw [usp, Ku.2.1, Ku.2.2]; exact I.arg3
  have r2 : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4 := by
    rw [usp, Ku.2.1, Ku.2.2]; exact I.arg2
  unfold stash
  refine WP.seq (wp_ldm rfl r3 fun u₁ U₁ => ?_)
  refine wp_ldm (by rw [U₁.other _ (by decide)]) (by rw [U₁.rd, U₁.wr]; exact r2) fun u₂ U₂ => ?_
  have K₂ : Keeps [.eax, .ecx] u u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have S₂ : Scr u₂ base size := Su.of_keeps K₂ (by decide)
  refine wp_storeS (S₂.ea (show 24 < size by omega)) (S₂.write (show 24 + 4 ≤ size by omega)) fun u₃ M₃ => ?_
  have S₃ : Scr u₃ base size := S₂.of_keeps (M₃.keeps [.eax]) (by decide)
  refine wp_storeS (S₃.ea (show 28 < size by omega)) (S₃.write (show 28 + 4 ≤ size by omega)) fun w M₄ =>
    WP.block_nil ?_
  have Sw : Scr w base size := S₃.of_keeps (M₄.keeps [.eax]) (by decide)
  have Mw : w.mem = ((u.mem.writeW (off base 24) (BitVec.ofNat 32 len)).writeW (off base 28) p) := by
    have e1 : u₂.gpr .eax = BitVec.ofNat 32 len := by rw [U₂.other _ (by decide), U₁.gpr]; exact a3
    have e2 : u₂.gpr .ecx = p := by rw [U₂.gpr, U₁.mem]; exact a2
    rw [M₄.mem, M₃.gpr, e2, M₃.mem, e1, U₂.mem, U₁.mem]
    rfl
  have OW : Outs base [(24, 4), (28, 4)] u.mem w.mem := by
    rw [Mw]
    exact (Outs.of_outside (writeW32_outside _ base _ (by decide)) (by simp)).trans
      (Outs.of_outside (writeW32_outside _ base _ (by decide)) (by simp))
  have W24 : w.mem.readW (off base 24) 32 = BitVec.ofNat 32 len := by
    rw [Mw, Mul.Outs.readW32 (Outs.of_outside (rs := [(28, 4)]) (writeW32_outside _ base _ (by decide)) (by simp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; omega) (by omega)]
    exact Mem.readW_writeW_self32 _ _ _
  have W28 : w.mem.readW (off base 28) 32 = p := by
    rw [Mw]; exact Mem.readW_writeW_self32 _ _ _
  have Kuw : Keeps [.eax, .ecx] u w := K₂.trans ((M₃.keeps _).trans (M₄.keeps _))
  -- the modulus is where the caller left it
  have Osw : Outs base [(8, 16), (24, 4), (28, 4)] s.mem w.mem :=
    (Outs.of_outside Ou (by simp)).trans (OW.mono (by simp))
  have hvw : wordsVal w.mem base (slot n 0) n = m := by
    rw [wordsVal_eq_val32, Osw.val32 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega) (by simp only [slot]; omega),
      ← wordsVal_eq_val32, hv]
  refine WP.seq (WP.mono (contextStart_ok Sw hn hz hvw (by omega) hodd) fun v ⟨Cv, _, Ov, Kv⟩ => ?_)
  have avoid (d : Nat) (hd : 24 ≤ d ∧ d + 4 ≤ 64) : ∀ r ∈ setupRanges n, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega
  have V28 : v.mem.readW (off base 28) 32 = p := by
    rw [Mul.Outs.readW32 Ov (avoid 28 (by omega)) (by omega), W28]
  have Sv' : Scr v base size := Cv.scr
  refine wp_movS (readSrc_sc Sv' (show 28 + 4 ≤ size by omega)) fun x X _ => WP.block_nil ?_
  have Cx : Context n m base size x :=
    Cv.outs_keep (ranges := []) X.keeps (by decide) (by decide) (fun _ _ => by rw [X.mem])
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
  have xrd : x.rd = s.rd := by rw [X.rd, Kv.2.1, Kuw.2.1, Ku.2.1]
  have xwr : x.wr = s.wr := by rw [X.wr, Kv.2.2, Kuw.2.2, Ku.2.2]
  have hsrc : LenSrc base size n x (.mem (sc lenAt)) len := by
    intro y hy _ _ O
    change readSrc y (.mem (sc 24)) = _
    rw [readSrc_sc hy (show 24 + 4 ≤ size by omega)]
    congr 1
    rw [Mul.Outs.readW32 O (fun r hr => by
        simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega) (by omega),
      X.mem, Mul.Outs.readW32 Ov (avoid 24 (by omega)) (by omega), W24]
  have inp : StreamInput x base (contextBytes n) p len :=
    ⟨I.input.fit, by rw [xrd, xwr]; exact I.input.read, I.input.far, by rw [xrd, xwr]; exact I.input.whole⟩
  -- every change so far is in the header and the context's slots
  have Osx : Outs base (scratch n) s.mem x.mem := by
    intro z hz
    have h0 := hz (0, 64) (List.mem_cons_self ..)
    have h1 := hz _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    dsimp only at h0 h1
    simp only [contextBytes, slot, stride] at h1
    rw [X.mem, Ov z (fun r hr => by
        simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega),
      Osw z (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega)]
  have Ox : Outside base 0 (contextBytes n) s.mem x.mem := fun z hz => Osx z fun r hr => by
    simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> simp only [contextBytes, slot, stride] at hz ⊢ <;> omega
  have savedX : Saved x.mem (off base) s.gpr slots := by
    intro q hq
    have hq' : 8 ≤ q.2 ∧ q.2 + 4 ≤ 24 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> decide
    rw [X.mem, Mul.Outs.readW32 Ov (fun r hr => by
        simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega) (by omega),
      Mul.Outs.readW32 OW (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> omega) (by omega)]
    exact Sv q hq
  have Kwx : Keeps powerClob w x := Kv.trans (X.keeps.mono (by decide))
  exact ⟨Cx, by rw [X.gpr]; exact V28, hsrc, inp, Osx, Ox, savedX,
    by rw [Kwx.1 _ (by decide), Kuw.1 _ (by decide)]; exact usp, xrd, xwr⟩

theorem body_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32}
    (I : In n s base size p len) (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm : 255 < m) (hodd : m % 2 = 1) :
    WP isa (reduceBody n) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) % m ∧
      Outs base (scratch n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hz' := hz
  simp only [contextBytes, slot, stride] at hz'
  unfold reduceBody
  refine WP.seq (WP.mono (prefix_ok I hz hn hv hm hodd) fun x R => ?_)
  refine WP.seq (WP.mono (reduceStream_ok R.ctx hm I.lenFit R.lenSrc R.input R.esi)
    fun y ⟨Cy, Vy, Oy, Ky⟩ => ?_)
  have Oxy : Outs base (scratch n) x.mem y.mem := VG.Proof.Mont.X86.Outs.widen Oy fun z hz r hr => by
    have h1 := hz _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    dsimp only at h1
    simp only [contextBytes, slot, stride] at h1
    simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega
  have savedY : Saved y.mem (off base) s.gpr slots := by
    intro q hq
    have hq' : 8 ≤ q.2 ∧ q.2 + 4 ≤ 24 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> decide
    rw [Mul.Outs.readW32 Oy (fun r hr => by
        simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega)
        (by have := I.entry.nowrap; omega)]
    exact R.saved q hq
  refine WP.mono (restore_ok Cy.scr (by omega) savedY)
    fun t R' => ⟨?_, ?_, R'.abi (by decide) (by decide) ?_, ?_, ?_⟩
  · rw [R'.mem, Vy, I.input.bytes R.outside]
  · rw [R'.mem]; exact R.outs.trans Oxy
  · rw [Ky.1 _ (by decide)]; exact R.esp
  · rw [R'.rd, Ky.2.1, R.rd]
  · rw [R'.wr, Ky.2.2, R.wr]

end VG.Proof.Dsa.X86.Red
