module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FragmentStep
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
public import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Cmac.Spec

/-! Each ciphertext byte has two destinations. The final word may overlap the
preceding word; a second write of the same byte leaves the invariant true. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64

abbrev off (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 i

structure Buffers where
  src : Addr
  key : Addr
  dst : Addr
  auth : Addr
  len : Nat

namespace Buffers
variable (b : Buffers)
abbrev reg (p : Addr) : Region := ⟨p,b.len⟩
abbrev outs : List Region := [b.reg b.dst, b.reg b.auth]
def byte (m : Mem) (j : Nat) := m (off b.src j) ^^^ m (off b.key j)
end Buffers

structure Layout (b : Buffers) (s : State) : Prop where
  lt : b.len < 2^64
  rd : Covers [b.reg b.src,b.reg b.key] (s.rd ++ s.wr)
  wr : Covers b.outs s.wr
  src : b.src = b.dst ∨ ∀ r ∈ b.outs, (b.reg b.src).Disjoint r
  key : ∀ r ∈ b.outs, (b.reg b.key).Disjoint r
  disj : (b.reg b.dst).Disjoint (b.reg b.auth)

structure Prefix (b : Buffers) (m : Mem) (i : Nat) (m' : Mem) : Prop where
  frame : Frame b.outs m m'
  dst : ∀ j < i, m' (off b.dst j) = b.byte m j
  auth : ∀ j < i, m' (off b.auth j) = b.byte m j
  unread : ∀ j, i ≤ j → j < b.len → m' (off b.dst j) = m (off b.dst j)

theorem Prefix.empty (b : Buffers) (m : Mem) : Prefix b m 0 m :=
  ⟨Frame.refl _ _, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩

structure Pointers (b : Buffers) (i : Nat) (t : State) : Prop where
  src : t.gpr .x0 = off b.src i
  key : t.gpr .x1 = off b.key i
  dst : t.gpr .x2 = off b.dst i
  auth : t.gpr .x3 = off b.auth i

theorem Layout.access {b s t} (h : Layout b s) {i n} (hin : i + n ≤ b.len) (p : Pointers b i t)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Access t n := by
  have lt := h.lt
  have c (a : Addr) := Offset.contains_base a hin (by omega : i < 2^64)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p.src, rd, wr]; exact h.rd _ _ ⟨_, by simp, c _⟩
  · rw [p.key, rd, wr]; exact h.rd _ _ ⟨_, by simp, c _⟩
  · rw [p.dst, wr]; exact h.wr _ _ ⟨_, by simp [Buffers.outs], c _⟩
  · rw [p.auth, wr]; exact h.wr _ _ ⟨_, by simp [Buffers.outs], c _⟩

/-- A write at offset 'start' extends the correct prefix even when its start
is before the old end, as in the overlapping last-word case. -/
theorem Prefix.putValue {b s m m' i start n} (lay : Layout b s)
    (h : Prefix b m i m') (v : BitVec (8*n)) (hstart : start ≤ i) (hcover : i ≤ start+n)
    (hend : start+n ≤ b.len) (fv : ∀ j < n, v.extractLsb' (8*j) 8 = b.byte m (start+j)) :
    Prefix b m (start+n) ((m'.write (off b.dst start) n v).write (off b.auth start) n v) := by
  have lt := lay.lt
  have c (a : Addr) := Offset.contains_base a hend (by omega : start < 2^64)
  have wr (a : Addr) (j : Nat) (hj : j < start+n) (m₁ : Mem) (old : ∀ k < i, m₁ (off a k) = b.byte m k) :
      m₁.write (off a start) n v (off a j) = b.byte m j := by
    by_cases hx : start ≤ j
    · have e := Offset.sub_toNat a hx (by omega : j < 2^64)
      simp only [off, Mem.write, e, show j - start < n by omega, ite_true]
      rw [fv _ (by omega), Nat.add_sub_of_le hx]
    · rw [Mem.write_apply]
      · exact old _ (by omega)
      · intro hbad
        have cb := (Region.contains_self (off a start) n).byte hbad
        have hd := Offset.disjoint a (d := j) (n := 1) (e := start) (k := n) (.inl (by omega))
          (by omega) (by omega)
        exact hd _ (Region.contains_self _ _) cb
  have da (j : Nat) (hj : j < b.len) :
      ¬ (off b.dst j - off b.auth start).toNat < n :=
    fun bad => lay.disj _ (Offset.contains_base _ (by omega) (by omega)) ((c b.auth).byte bad)
  refine ⟨(h.frame.write (r := b.reg b.dst) (by simp [Buffers.outs]) _ (c _)).write
    (r := b.reg b.auth) (by simp [Buffers.outs]) _ (c _), ?_, ?_, ?_⟩
  · intro j hj
    rw [Mem.write_apply (da j (by omega))]
    exact wr _ _ hj _ h.dst
  · intro j hj
    refine wr _ _ hj _ fun k hk => ?_
    rw [Mem.write_apply]
    · exact h.auth k hk
    · intro bad
      by_cases he : k < b.len
      · exact lay.disj _ ((c _).byte bad) (Offset.contains_base _ (by omega) (by omega))
      · -- Only bytes before the new write need a prior value.
        exact False.elim (by omega)
  · intro j hj hjl
    rw [Mem.write_apply (da j hjl), Mem.write_apply]
    · exact h.unread j (by omega) hjl
    · rw [off, off, Offset.sub_toNat _ (by omega) (by omega)]; omega

theorem Prefix.sourceWord {b s t m i n k} (h : Prefix b m i t.mem) (lay : Layout b s)
    (p : Pointers b i t) (hend : i+k+n ≤ b.len) (j : Nat) (hj : j < n) :
    (wordAt t n (BitVec.ofNat 64 k)).extractLsb' (8*j) 8 = b.byte m (i+k+j) := by
  simp only [wordAt,p.src,p.key,BitVec.extractLsb'_xor,Mem.extractLsb'_read _ _ hj,
    off,Offset.add_add,Buffers.byte]
  have bound : i+k+j < b.len := by omega
  have src : t.mem (off b.src (i+k+j)) = m (off b.src (i+k+j)) := by
    rcases lay.src with eq | apart
    · rw [eq]; exact h.unread _ (by omega) bound
    · exact h.frame.bytes apart (Nat.le_of_lt lay.lt) bound
  rw [src, h.frame.bytes lay.key (Nat.le_of_lt lay.lt) bound]

theorem Prefix.put {b s t m i n} (lay : Layout b s)
    (h : Prefix b m i t.mem) (p : Pointers b i t) (hend : i+n ≤ b.len) :
    Prefix b m (i+n) (putBoth t n) := by
  unfold putBoth
  rw [p.dst, p.auth]
  apply h.putValue lay _ (Nat.le_refl _) (by omega) hend
  intro j hj
  simpa [wordAt]
    using h.sourceWord (k := 0) lay p (by simpa only [Nat.add_zero] using hend) j hj


end VG.Proof.AesGcm.AArch64.DirectGather.Fragment

/-! After the descriptor is decoded, four pointers walk through the source,
keystream, ciphertext and authentication input. The number of correct bytes
may exceed the pointer position briefly in the overlapping last word. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64

abbrev workRegs : List Reg := [.x0,.x1,.x2,.x3,.x12,.x13,.x14,.x15]

structure Cursor (b : Buffers) (s : State) (pos doneBytes : Nat) (t : State) : Prop
    extends Kept s t workRegs where
  ptrs : Pointers b pos t
  written : Prefix b s.mem doneBytes t.mem

theorem Cursor.wrote {b s t u i n rs} (c : Cursor b s i i t) (lay : Layout b s)
    (w : Wrote t n rs u) (regs : ∀ r ∈ rs, r = .x14 ∨ r = .x15)
    (hend : i+n ≤ b.len) :
    Cursor b s i (i+n) u ∧ u.gpr .x12 = t.gpr .x12 ∧ u.gpr .x13 = t.gpr .x13 := by
  have kept {r : Reg} (h : r ≠ .x14 ∧ r ≠ .x15) := w.gpr r fun h' => (regs r h').elim h.1 h.2
  refine ⟨⟨⟨fun r h => ?_, w.sp.trans c.sp, w.rd.trans c.rd, w.wr.trans c.wr⟩,
    ⟨(kept (by decide)).trans c.ptrs.src, (kept (by decide)).trans c.ptrs.key,
     (kept (by decide)).trans c.ptrs.dst, (kept (by decide)).trans c.ptrs.auth⟩, ?_⟩,
    kept (by decide), kept (by decide)⟩
  · exact (kept ⟨fun e => h (by simp [workRegs,e]), fun e => h (by simp [workRegs,e])⟩).trans (c.gpr r h)
  · rw [w.mem]; exact c.written.put lay c.ptrs hend

/-- Advance four byte pointers by an immediate. -/
theorem advance_ok {b s p i t} (c : Cursor b s p i t) (k : Nat) (hk : k < 4096) :
    WP isa (.block (advance k)) t fun u =>
      Cursor b s (p+k) i u ∧ u.gpr .x12 = t.gpr .x12 ∧ u.gpr .x13 = t.gpr .x13 := by
  apply WP.of_runBlock
  simp only [advance, ptr, runBlock_cons, runStep_some, runBlock_nil, exec, hk, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨fun r hr => ?_, c.sp, c.rd, c.wr⟩, ?_, c.written⟩, rfl, rfl⟩
  · have hh : r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [workRegs,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩
    simpa only [gpr_write, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, ite_false] using c.gpr r hr
  · constructor <;> simp only [gpr_write, State.read, Size.bits, BitVec.setWidth_eq, reduceCtorEq,
      ite_true, ite_false, c.ptrs.src, c.ptrs.key, c.ptrs.dst, c.ptrs.auth, off, Offset.add_add]

abbrev countReg (block : Bool) : Reg := if block then .x13 else .x12
abbrev otherReg (block : Bool) : Reg := if block then .x12 else .x13
abbrev width (block : Bool) : Nat := if block then 16 else 1

theorem decrement_ok {b s p i t} (c : Cursor b s p i t) (block : Bool) :
    WP isa (.block [.subImm .x (countReg block) (countReg block) 1]) t fun u =>
      Cursor b s p i u ∧ u.gpr (countReg block) = t.gpr (countReg block) - 1 ∧
      u.gpr (otherReg block) = t.gpr (otherReg block) := by
  cases block <;> apply WP.of_runBlock <;>
    simp only [countReg, otherReg, Bool.false_eq_true, ↓reduceIte, runBlock_cons, runStep_some,
      runBlock_nil, exec, Nat.reduceLT, Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨⟨⟨fun r hr => ?_, c.sp, c.rd, c.wr⟩, ⟨c.ptrs.src,c.ptrs.key,c.ptrs.dst,c.ptrs.auth⟩, c.written⟩, rfl, rfl⟩
    first
    | exact (gpr_write_of_ne _ _ _ (fun he => hr (List.mem_of_mem_tail (by simp [he])))).trans (c.gpr r hr)
    | simp only [gpr_write]; split
      · rename_i h; exact False.elim (hr (by simp [workRegs,h]))
      · exact c.gpr r hr

abbrev step (block : Bool) := if block then blockStep else byteStep

theorem step_ok {b s i t} (c : Cursor b s i i t) (lay : Layout b s) (block : Bool)
    (hend : i + width block ≤ b.len) :
    WP isa (.block (step block)) t fun u =>
      Cursor b s (i + width block) (i + width block) u ∧
      u.gpr (countReg block) = t.gpr (countReg block) - 1 ∧ u.gpr (otherReg block) = t.gpr (otherReg block) := by
  have hacc := lay.access hend c.ptrs c.rd c.wr
  cases block
  all_goals
    simp only [step, Bool.false_eq_true, ↓reduceIte, byteStep, blockStep, List.append_assoc]
    rw [WP.block_append_iff]
    first | refine (byteData_ok _ hacc).mono fun t₁ w => ?_ | refine (blockData_ok _ hacc).mono fun t₁ w => ?_
    obtain ⟨c₁,h12,h13⟩ := c.wrote lay w (by simp) hend
    rw [WP.block_append_iff]
    refine (advance_ok c₁ _ (by decide)).mono fun t₂ ⟨c₂,h12',h13'⟩ => ?_
    first
    | refine (decrement_ok c₂ false).mono fun _ ⟨c₃,a,d⟩ => ⟨c₃, ?_, ?_⟩
    | refine (decrement_ok c₂ true).mono fun _ ⟨c₃,a,d⟩ => ⟨c₃, ?_, ?_⟩
    all_goals simp_all only [countReg, otherReg, ↓reduceIte, Bool.false_eq_true]

/-- Iterate either of the exact-width pieces. A positive count is passed to
the loop; its caller handles zero before entry. -/
theorem loop_ok {b s t pos cnt} (block : Bool) (c : Cursor b s pos pos t) (lay : Layout b s)
    (count : t.gpr (countReg block) = BitVec.ofNat 64 cnt) (posCnt : 0 < cnt)
    (last : pos + cnt * width block ≤ b.len) :
    WP isa (.loop (.block (step block)) (.nonzero .x (countReg block))) t fun u =>
      Cursor b s (pos + cnt*width block) (pos + cnt*width block) u ∧
      u.gpr (otherReg block) = t.gpr (otherReg block) := by
  let lastPos := pos + cnt * width block
  have lt := lay.lt
  refine WP.loop (M := isa) (body := .block (step block)) (c := .nonzero .x (countReg block))
    (fun (k : Nat) u => ∃ j, j + k*width block = lastPos ∧ 0 < k ∧
      Cursor b s j j u ∧ u.gpr (countReg block) = BitVec.ofNat 64 k ∧
      u.gpr (otherReg block) = t.gpr (otherReg block)) ?_ cnt t ⟨pos,rfl,posCnt,c,count,rfl⟩
  rintro k u ⟨j,hj,hk,cur,cntEq,other⟩
  have endOk : j + width block ≤ b.len := by
    dsimp [lastPos] at hj; cases block <;> simp only [width, ↓reduceIte, Bool.false_eq_true, Nat.mul_one] at * <;> omega
  refine (step_ok cur lay block endOk).mono fun u' ⟨cur',cnt',other'⟩ => ?_
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [cntEq, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega),
    Nat.add_one_sub_one] at cnt'
  rw [Nat.succ_mul] at hj
  have ke : k < 2 ^ 64 := by
    dsimp [lastPos] at hj; cases block <;> simp only [width, ↓reduceIte, Bool.false_eq_true, Nat.mul_one] at * <;> omega
  have ev := eval_nonzero cnt' ke
  by_cases h0 : k = 0
  · subst h0
    simp only [Nat.zero_mul, Nat.zero_add] at hj
    exact Or.inl ⟨by simpa using ev, by simpa only [hj] using cur', other'.trans other⟩
  · exact Or.inr ⟨by simpa [h0] using ev, k, Nat.lt_succ_self _, j + width block,
      by rw [← hj]; omega, Nat.pos_of_ne_zero h0, cur', cnt', other'.trans other⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Fragment

/-! The tail uses overlapping four- or eight-byte writes inside the same
fragment. Both stores draw from untouched plaintext and keystream bytes. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.DirectGather

abbrev overlap (sz : Size) : Prog isa :=
  .block (xorEnds sz (sz.bits/8) ++ advance (sz.bits/8))

theorem overlap_ok {b s i t n} (sz : Size) (c : Cursor b s i i t) (lay : Layout b s)
    (cnt : t.gpr .x12 = BitVec.ofNat 64 n) (h₁ : sz.bits/8 ≤ n) (h₂ : n ≤ 2*(sz.bits/8))
    (hend : i+n ≤ b.len) :
    WP isa (overlap sz) t (Cursor b s (i+n) (i+n)) := by
  let k := sz.bits/8
  let d := BitVec.ofNat 64 (n-k)
  have lt := lay.lt
  have e : i+(n-k)+k = i+n := by dsimp [k]; omega
  have hfirst : i+k ≤ b.len := by dsimp [k]; omega
  have hlast : i+(n-k)+k ≤ b.len := e ▸ hend
  have q : OffsetAccess t d k := by
    refine ⟨?_,?_,?_,?_⟩
    all_goals
      simp only [c.ptrs.src,c.ptrs.key,c.ptrs.dst,c.ptrs.auth,c.rd,c.wr,d,off,Offset.add_add]
    · exact lay.rd _ _ ⟨_,by simp, Offset.contains_base _ hlast (by omega)⟩
    · exact lay.rd _ _ ⟨_,by simp, Offset.contains_base _ hlast (by omega)⟩
    · exact lay.wr _ _ ⟨_,by simp [Buffers.outs], Offset.contains_base _ hlast (by omega)⟩
    · exact lay.wr _ _ ⟨_,by simp [Buffers.outs], Offset.contains_base _ hlast (by omega)⟩
  rw [show overlap sz = .block (xorEnds sz k ++ advance k) from rfl, WP.block_append_iff]
  refine (xorEnds_ok sz t d (lay.access hfirst c.ptrs c.rd c.wr) q
    (by rw [cnt,Offset.ofNat_sub_ofNat h₁])).mono fun u ⟨kept,regs,mem⟩ => ?_
  have first := c.written.putValue lay (wordAt t k 0) (Nat.le_refl _) (by omega) hfirst
    (fun j hj => by simpa using
      c.written.sourceWord (k := 0) lay c.ptrs (by simpa using hfirst) j hj)
  have both := first.putValue lay (wordAt t k d) (start := i+(n-k)) (by dsimp [k]; omega)
    (by dsimp [k]; omega) hlast (fun j hj => c.written.sourceWord lay c.ptrs hlast j hj)
  have cur : Cursor b s (i+(n-k)) (i+n) u := by
    refine ⟨⟨fun r hr => (kept.gpr _ hr).trans (c.gpr _ hr), kept.sp.trans c.sp,
      kept.rd.trans c.rd,kept.wr.trans c.wr⟩, ?_, ?_⟩
    · constructor <;> simp only [regs .x0 (by decide),regs .x1 (by decide),regs .x2 (by decide),regs .x3 (by decide),c.ptrs.src,c.ptrs.key,c.ptrs.dst,c.ptrs.auth,
        off,d,Offset.add_add]
    · rw [mem,← e]
      simpa [placeWord,c.ptrs.dst,c.ptrs.auth,off,d,Offset.add_add] using both
  exact (advance_ok cur k (by cases sz <;> decide)).mono fun _ ⟨done',_,_⟩ => by simpa only [e] using done'

abbrev tail : Prog isa :=
  .seq (.block [.lsr .x .x14 .x12 3]) <|
    .ite (.nonzero .x .x14) (overlap .x) <|
    .seq (.block [.lsr .x .x14 .x12 2]) <|
    .ite (.nonzero .x .x14) (overlap .w) (.loop (.block byteStep) (.nonzero .x .x12))

theorem shift_ok {b s p i t n} (c : Cursor b s p i t) (cnt : t.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n < 2^64) (sh : Nat) (hs : sh < 64) :
    WP isa (.block [.lsr .x .x14 .x12 sh]) t fun u =>
      Cursor b s p i u ∧ u.gpr .x14 = BitVec.ofNat 64 (n/2^sh) ∧ u.gpr .x12 = t.gpr .x12 := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,Size.bits,hs,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨⟨⟨fun r hr => ?_, c.sp, c.rd, c.wr⟩,
    ⟨c.ptrs.src,c.ptrs.key,c.ptrs.dst,c.ptrs.auth⟩, c.written⟩, ?_, rfl⟩
  · have hh : r ≠ .x14 := fun he => hr (by simp [he,workRegs])
    simp only [gpr_write,hh,ite_false,c.gpr r hr]
  · simp [gpr_write,State.read,Size.bits,cnt,lsr_ofNat _ _ hn]

theorem tail_ok {b s i t n} (c : Cursor b s i i t) (lay : Layout b s)
    (cnt : t.gpr .x12 = BitVec.ofNat 64 n) (hn : 0 < n) (h16 : n < 16) (hend : i+n ≤ b.len) :
    WP isa tail t (Cursor b s (i+n) (i+n)) := by
  unfold tail
  refine WP.seq ((shift_ok c cnt (by omega) 3 (by decide)).mono fun u ⟨cur,flag,left⟩ => ?_)
  refine WP.ite _ (eval_nonzero flag (by omega)) (fun hy => ?_) (fun hz => ?_)
  · have h : n/8 ≠ 0 := by simpa using hy
    exact overlap_ok .x cur lay (left.trans cnt) (by change 8 ≤ n; omega) (by change n ≤ 16; omega) hend
  · refine WP.seq ((shift_ok cur (left.trans cnt) (by omega) 2 (by decide)).mono fun v ⟨cur',flag',left'⟩ => ?_)
    refine WP.ite _ (eval_nonzero flag' (by omega)) (fun hy => ?_) (fun _ => ?_)
    · have h : n/4 ≠ 0 := by simpa using hy
      have h' : n/8 = 0 := by simpa using hz
      exact overlap_ok .w cur' lay (left'.trans (left.trans cnt)) (by change 4 ≤ n; omega) (by change n ≤ 8; omega) hend
    · exact (loop_ok false cur' lay (left'.trans (left.trans cnt)) hn (by simpa [width] using hend)).mono
        fun _ ⟨u',_⟩ => by simpa [width] using u'

end VG.Proof.AesGcm.AArch64.DirectGather.Fragment

/-! Encryption of one short-record descriptor. The output is appended to
the caller's ciphertext and the GHASH input at matching offsets. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.DirectGather

abbrev decode : List Instr :=
  [.ldr .x .x0 .x6 0, .ldr .x .x12 .x6 8, ptr .x6 .x6 16,
   .lsr .x .x13 .x12 4, imm .x14 15, .logic .and .x .x12 .x12 .x14]

abbrev pieceRegs : List Reg := .x6 :: workRegs

structure PiecePre (b : Buffers) (s : State) : Prop extends Layout b s where
  desc : InRegions (s.rd ++ s.wr) (s.gpr .x6) 8
  count : InRegions (s.rd ++ s.wr) (s.gpr .x6 + BitVec.ofNat 64 8) 8
  source : s.mem.readW (s.gpr .x6) 64 = b.src
  size : s.mem.readW (s.gpr .x6 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 b.len
  keyPtr : s.gpr .x1 = b.key
  dstPtr : s.gpr .x2 = b.dst
  authPtr : s.gpr .x3 = b.auth

structure Decoded (b : Buffers) (s t : State) : Prop extends Kept s t pieceRegs where
  ptrs : Pointers b 0 t
  desc : t.gpr .x6 = s.gpr .x6 + 16
  whole : t.gpr .x13 = BitVec.ofNat 64 (b.len / 16)
  rest : t.gpr .x12 = BitVec.ofNat 64 (b.len % 16)
  mem : t.mem = s.mem

set_option linter.unusedSimpArgs false in
theorem decode_ok {b s} (h : PiecePre b s) : WP isa (.block decode) s (Decoded b s) := by
  apply WP.of_runBlock
  simp only [decode,ptr,imm,runBlock_cons,runStep_some,runBlock_nil,exec,addr,State.load,State.read,Size.bits,
    Size.bytes,Nat.reduceMul,Nat.reduceDiv,Nat.reduceMod,Nat.reduceLT,and_self,↓reduceIte,BitVec.add_zero,
    h.desc,h.count,Option.map_some,Option.bind_some,gpr_write,mem_write,rd_write,wr_write,BitVec.setWidth_eq,
    reduceCtorEq,Option.some.injEq,exists_eq_left']
  have src : s.mem.read (s.gpr .x6) 8 = b.src := h.source
  have len : s.mem.read (s.gpr .x6 + BitVec.ofNat 64 8) 8 = BitVec.ofNat 64 b.len := h.size
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_, rfl, ?_, ?_, rfl⟩
  · have hs : r ≠ .x0 ∧ r ≠ .x6 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 := by
      simp only [pieceRegs,workRegs,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      exact ⟨hr.2.1,hr.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.1⟩
    simp [gpr_write,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2]
  · constructor <;> simp [off,gpr_write,src,h.keyPtr,h.dstPtr,h.authPtr]
  · simpa [gpr_write,State.read,len] using lsr_ofNat b.len 4 h.lt
  · simp only [State.read,gpr_write,Size.bits,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,len]
    change (BitVec.ofNat 64 b.len &&& BitVec.ofNat 64 15) = _
    rw [and15,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h.lt]

structure PiecePost (b : Buffers) (s t : State) : Prop extends Kept s t pieceRegs where
  desc : t.gpr .x6 = s.gpr .x6 + 16
  ptrs : Pointers b b.len t
  written : Prefix b s.mem b.len t.mem

/-- The fragment after its source and length have been decoded. Gather and
contiguous callers share the same loop, writes and carry into the byte tail. -/
abbrev pieceSuffix : Prog isa :=
  .seq (.ite (.zero .x .x13) (.block []) (.loop (.block blockStep) (.nonzero .x .x13)))
    (.ite (.zero .x .x12) (.block []) tail)

theorem pieceSuffix_ok {b u} (L : Layout b u) (pointers : Pointers b 0 u)
    (full : u.gpr .x13 = BitVec.ofNat 64 (b.len/16))
    (tailCount : u.gpr .x12 = BitVec.ofNat 64 (b.len%16)) :
    WP isa pieceSuffix u (Cursor b u b.len b.len) := by
  have init : Cursor b u 0 0 u :=
    ⟨⟨fun _ _ => rfl,rfl,rfl,rfl⟩,pointers,Prefix.empty b _⟩
  let whole := (b.len/16)*16
  have fit : whole + b.len % 16 = b.len := by dsimp [whole]; omega
  have hlt := L.lt
  have blocks : WP isa (.ite (.zero .x .x13) (.block []) (.loop (.block blockStep) (.nonzero .x .x13))) u
      fun v => Cursor b u whole whole v ∧ v.gpr .x12 = BitVec.ofNat 64 (b.len%16) := by
    refine WP.ite _ (eval_zero full (by omega)) (fun hz => ?_) (fun hp => ?_)
    · have z : b.len / 16 = 0 := of_decide_eq_true hz
      exact WP.block_nil ⟨by simpa [whole,z] using init,tailCount⟩
    · have z := of_decide_eq_false hp
      refine (loop_ok true init L full (by omega) (by change 0 + b.len /16 * 16 ≤ b.len; omega)).mono
        fun _ ⟨c,rest⟩ => ⟨by simpa [whole,width] using c,rest.trans tailCount⟩
  refine WP.seq (blocks.mono fun v ⟨c,rest⟩ => ?_)
  have bytes : WP isa (.ite (.zero .x .x12) (.block []) tail) v (Cursor b u b.len b.len) := by
    refine WP.ite _ (eval_zero rest (by omega)) (fun hz => ?_) (fun hp => ?_)
    · have z := of_decide_eq_true hz
      exact WP.block_nil (by simpa only [show whole = b.len by omega] using c)
    · have z := of_decide_eq_false hp
      simpa only [fit] using tail_ok c L rest (by omega) (by omega) (Nat.le_of_eq fit)
  exact bytes

theorem shortPiece_ok {b s} (h : PiecePre b s) : WP isa shortPiece s (PiecePost b s) := by
  change WP isa (.seq (.block decode) (.seq
      (.ite (.zero .x .x13) (.block []) (.loop (.block blockStep) (.nonzero .x .x13)))
      (.ite (.zero .x .x12) (.block []) tail))) s _
  refine WP.seq ((decode_ok h).mono fun u d => ?_)
  have L : Layout b u :=
    ⟨h.lt, by rw [d.rd,d.wr]; exact h.rd, by rw [d.wr]; exact h.wr, h.src,h.key,h.disj⟩
  refine (pieceSuffix_ok L d.ptrs d.whole d.rest).mono fun w out => ⟨⟨fun r hr => ?_,out.sp.trans d.sp,out.rd.trans d.rd,out.wr.trans d.wr⟩,
    (out.gpr .x6 (by decide)).trans d.desc,out.ptrs,by simpa only [d.mem] using out.written⟩
  exact (out.gpr r fun he => hr (List.mem_cons_of_mem _ he)).trans (d.gpr _ hr)

/-- The contiguous entry receives its source and length in registers. All
subsequent instructions are the same fragment as for a gather descriptor. -/
theorem directPiece_ok {b s} {source : Reg} (h : Layout b s) (src : s.gpr source = b.src)
    (len : s.gpr .x26 = BitVec.ofNat 64 b.len) (key : s.gpr .x1 = b.key)
    (dst : s.gpr .x2 = b.dst) (auth : s.gpr .x3 = b.auth) :
    WP isa (shortPieceWith [mov .x0 source,mov .x12 .x26]) s (Cursor b s b.len b.len) := by
  let head : List Instr := [mov .x0 source,mov .x12 .x26,.lsr .x .x13 .x12 4,
    imm .x14 15,.logic .and .x .x12 .x12 .x14]
  change WP isa (.seq (.block head) pieceSuffix) s _
  have initial : WP isa (.block head) s fun t =>
      Kept s t workRegs ∧ t.mem = s.mem ∧ Pointers b 0 t ∧
      t.gpr .x13 = BitVec.ofNat 64 (b.len/16) ∧ t.gpr .x12 = BitVec.ofNat 64 (b.len%16) := by
    apply WP.of_runBlock
    refine ⟨_,by arun [head],?_⟩
    refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl⟩,rfl,?_,?_,?_⟩
    · have hs : r ≠ .x0 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 := by
        simp only [workRegs,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
        exact ⟨hr.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1⟩
      simp [gpr_write,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2]
    · constructor <;> simp [off,gpr_write,src,key,dst,auth]
    · simpa [gpr_write,State.read,len] using lsr_ofNat b.len 4 h.lt
    · simp only [gpr_write,Size.bits,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,len,BitVec.add_zero]
      change (BitVec.ofNat 64 b.len &&& BitVec.ofNat 64 15) = _
      rw [and15,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h.lt]
  refine WP.seq (initial.mono fun u ⟨kept,mem,ptrs,full,tailCount⟩ => ?_)
  have lay : Layout b u :=
    ⟨h.lt,by rw [kept.rd,kept.wr]; exact h.rd,by rw [kept.wr]; exact h.wr,h.src,h.key,h.disj⟩
  refine (pieceSuffix_ok lay ptrs full tailCount).mono fun w out =>
    ⟨⟨fun r hr => (out.gpr _ hr).trans (kept.gpr _ hr),out.sp.trans kept.sp,
      out.rd.trans kept.rd,out.wr.trans kept.wr⟩,out.ptrs,by simpa only [mem] using out.written⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Fragment

/-! Correct source position for each encrypted descriptor, including empty
descriptors and descriptors beginning in a partially used counter block. -/

public section

namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.Spec.Gcm VG.Proof.Gcm VG.Proof.AesGcm.AArch64.Gather
open VG.Spec.Aes (bytesAt)

theorem encrypt_next_piece (cipher : Block → Block) (icb : Block) (m : Mem) (src : Addr) (i : Nat) :
    gctr cipher icb (gathered 64 m src (i + 1)) =
      gctr cipher icb (gathered 64 m src i) ++
      xorKs cipher icb (gatheredLen 64 m src i) (bytesAt m (sb m src i) (sl m src i)) := by
  rw [pt_succ, gctr_append, length_gathered]

end VG.Proof.AesGcm.AArch64.DirectGather

/-! The descriptor loop appends each piece to both outputs. All plaintext
reads refer to the caller's original memory, even when source slices overlap. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather
open VG.Spec.Gcm (gathered gatheredLen)
open VG.Proof.AesGcm.AArch64.Gather (sb sl pt_succ gl_succ gl_mono slice_mem)

abbrev ds (s : State) := s.gpr .x6
abbrev num (s : State) := (s.gpr .x7).toNat
abbrev gl (s : State) (i : Nat) := gatheredLen 64 s.mem (ds s) i
abbrev pt (s : State) (i : Nat) := gathered 64 s.mem (ds s) i
abbrev total (s : State) := gl s (num s)
abbrev dout (s : State) : Region := ⟨s.gpr .x2,total s⟩
abbrev gout (s : State) : Region := ⟨s.gpr .x3,total s⟩
abbrev stream (s : State) : Region := ⟨s.gpr .x1,total s⟩
abbrev descR (s : State) : Region := ⟨ds s,16*num s⟩
abbrev outRegions (s : State) := [dout s,gout s]
abbrev readRegions (s : State) := descR s :: stream s :: Sig.listed 64 s.mem .u8 (ds s) (num s)
abbrev loopRegs : List Reg := .x7 :: pieceRegs

def curBuf (s : State) (i : Nat) : Buffers :=
  ⟨sb s.mem (ds s) i, off (s.gpr .x1) (gl s i), off (s.gpr .x2) (gl s i), off (s.gpr .x3) (gl s i),
    sl s.mem (ds s) i⟩

structure LoopPre (s : State) : Prop where
  len : total s < 2^64
  descriptors : 16*num s < 2^64
  rd : Covers (readRegions s) (s.rd ++ s.wr)
  wr : Covers (outRegions s) s.wr
  apart : ∀ a ∈ [descR s,stream s], ∀ b ∈ outRegions s, a.Disjoint b
  source : ∀ i < num s, (i = 0 ∧ (curBuf s i).src = (curBuf s i).dst) ∨
    ∀ r ∈ outRegions s, ((curBuf s i).reg (curBuf s i).src).Disjoint r
  disj : (dout s).Disjoint (gout s)

structure AtDesc (s : State) (i : Nat) (t : State) : Prop extends Kept s t loopRegs where
  desc : t.gpr .x6 = off (ds s) (16*i)
  count : t.gpr .x7 = BitVec.ofNat 64 (num s-i)
  key : t.gpr .x1 = off (s.gpr .x1) (gl s i)
  dst : t.gpr .x2 = off (s.gpr .x2) (gl s i)
  auth : t.gpr .x3 = off (s.gpr .x3) (gl s i)
  frame : Frame (outRegions s) s.mem t.mem
  outD : ∀ j < gl s i, t.mem (off (s.gpr .x2) j) = (pt s i).getD j 0 ^^^ s.mem (off (s.gpr .x1) j)
  outG : ∀ j < gl s i, t.mem (off (s.gpr .x3) j) = (pt s i).getD j 0 ^^^ s.mem (off (s.gpr .x1) j)
  firstMem : i = 0 → t.mem = s.mem

theorem AtDesc.init (s : State) : AtDesc s 0 s := by
  have h0 : gl s 0 = 0 := rfl
  refine ⟨⟨fun _ _ => rfl,rfl,rfl,rfl⟩,by simp [off],by simp [num],?_,?_,?_,Frame.refl _ _,
    fun _ h => (Nat.not_lt_zero _ (h0 ▸ h)).elim, fun _ h => (Nat.not_lt_zero _ (h0 ▸ h)).elim,fun _ => rfl⟩ <;> simp [off,h0]

theorem curBound {s : State} {i : Nat} (hi : i < num s) :
    gl s i + (curBuf s i).len ≤ total s := by
  change gl s i + sl s.mem (ds s) i ≤ _
  rw [← gl_succ]
  exact gl_mono _ _ hi

theorem curSub {s : State} {i : Nat} (hi : i < num s) :
    ∀ a ∈ (curBuf s i).outs, ∃ r ∈ outRegions s, Region.Sub a r := by
  intro a ha
  simp only [Buffers.outs,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  · exact ⟨dout s, by simp, Offset.sub_base _ (curBound hi)⟩
  · exact ⟨gout s, by simp, Offset.sub_base _ (curBound hi)⟩

theorem piecePre {s i t} (pre : LoopPre s) (hi : i < num s) (atD : AtDesc s i t) :
    PiecePre (curBuf s i) t := by
  let b := curBuf s i
  have bound := curBound hi
  have total_lt := pre.len
  have desc_lt := pre.descriptors
  have readSrc : b.reg b.src ∈ readRegions s := List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| slice_mem _ _ hi
  have rd0 (d : Nat) (hd : d+8 ≤ 16*num s) : InRegions (s.rd ++ s.wr) (off (ds s) d) 8 :=
    pre.rd _ _ ⟨descR s, by simp,Offset.contains_base _ hd (by omega)⟩
  have descEq (d : Nat) (hd : d+8 ≤ 16*num s) : t.mem.readW (off (ds s) d) 64 = s.mem.readW (off (ds s) d) 64 :=
    atD.frame.readW (r := descR s) (Offset.contains_base _ hd (by omega)) (pre.apart _ (by simp)) (by decide)
  have rdSrc := Covers.of_mem (rs := [b.reg b.src]) (rs' := readRegions s) (by simpa using readSrc)
  have rdK : Covers [b.reg b.key] (readRegions s) := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨stream s, by simp,gl s i,rfl,bound⟩
  have wr : Covers b.outs (outRegions s) := Covers.of_sub fun r hr => by
    simp only [Buffers.outs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨dout s,by simp,gl s i,rfl,bound⟩
    · exact ⟨gout s,by simp,gl s i,rfl,bound⟩
  have sep (R : Region) (hR : R ∈ [descR s,stream s]) (A : Region) (hA : Region.Sub A R) (B : Region) (hb : B ∈ b.outs) :
      A.Disjoint B := by
    obtain ⟨B',hm,hs⟩ := curSub hi _ hb
    exact ((pre.apart R hR B' hm).sub_left hA).sub_right hs
  refine ⟨⟨by omega, ?_, ?_, ?_,
    sep _ (show stream s ∈ [descR s,stream s] by simp) _ (Offset.sub_base _ bound),
    (pre.disj.sub_left (Offset.sub_base _ bound)).sub_right (Offset.sub_base _ bound)⟩,
    ?_,?_,?_,?_,atD.key,atD.dst,atD.auth⟩
  · rw [atD.rd,atD.wr]; exact (rdSrc.trans pre.rd).pair (rdK.trans pre.rd)
  · rw [atD.wr]; exact wr.trans pre.wr
  · rcases pre.source i hi with same | apart
    · exact Or.inl same.2
    · exact Or.inr fun B hb => by
        obtain ⟨B',hm,hs⟩ := curSub hi _ hb
        exact (apart B' hm).sub_right hs
  · rw [atD.rd,atD.wr,atD.desc]; exact rd0 _ (by omega)
  · rw [atD.rd,atD.wr,atD.desc, off,Offset.add_add]
    exact rd0 _ (by omega)
  · rw [atD.desc,descEq _ (by omega)]; rfl
  · rw [atD.desc,off,Offset.add_add,descEq (16*i+8) (by omega)]
    change _ = BitVec.ofNat 64 (s.mem.readW (off (ds s) (16*i) + BitVec.ofNat 64 8) 64).toNat
    rw [off,Offset.add_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]

/-- The encrypted slice extends a previously correct output. Bytes before it
are outside this piece's frame. -/
theorem extendOutput {s i t u} (pre : LoopPre s) (hi : i < num s) (cur : AtDesc s i t)
    (piece : PiecePost (curBuf s i) t u) (dest : Addr)
    (hd : dest = s.gpr .x2 ∨ dest = s.gpr .x3)
    (old : ∀ j < gl s i, t.mem (off dest j) = (pt s i).getD j 0 ^^^ s.mem (off (s.gpr .x1) j))
    (new : ∀ j < (curBuf s i).len, u.mem (off (off dest (gl s i)) j) = (curBuf s i).byte t.mem j) :
    ∀ j < gl s (i+1), u.mem (off dest j) = (pt s (i+1)).getD j 0 ^^^ s.mem (off (s.gpr .x1) j) := by
  intro j hj
  have bound := curBound hi
  have lt := pre.len
  have hn := gl_succ s.mem (ds s) i
  change gl s (i+1) = gl s i + (curBuf s i).len at hn
  rw [hn] at hj
  have hp : pt s (i+1) = pt s i ++ Spec.Aes.bytesAt s.mem (curBuf s i).src (curBuf s i).len := pt_succ _ _ _
  have hl : (pt s i).length = gl s i := Proof.Gcm.length_gathered _ _ _ _
  rw [hp,List.getD_eq_getElem?_getD]
  by_cases hj' : j < gl s i
  · rw [List.getElem?_append_left (hl ▸ hj'), ← List.getD_eq_getElem?_getD, ← old _ hj']
    apply piece.written.frame
    intro r hr
    simp only [Buffers.outs,List.mem_cons,List.not_mem_nil,or_false] at hr
    have earlier (p : Addr) :
        ¬ (⟨off p (gl s i),(curBuf s i).len⟩ : Region).Contains (off p j) 1 :=
      fun hc => (Offset.disjoint p (d := j) (n := 1) (e := gl s i) (k := (curBuf s i).len)
        (.inl (by omega)) (by omega) (by omega)) _ (Region.contains_self _ _) hc
    have small (p : Addr) := Offset.sub_base p bound
    rcases hd with rfl|rfl <;> rcases hr with rfl|rfl
    · exact earlier _
    · exact fun hc => pre.disj _ (Offset.contains_base _ (by omega) (by omega)) (small _ _ hc)
    · exact fun hc => pre.disj _ (small _ _ hc) (Offset.contains_base _ (by omega) (by omega))
    · exact earlier _
  · let k := j - gl s i
    have e : gl s i + k = j := by dsimp [k]; omega
    have hk : k < (curBuf s i).len := by dsimp [k]; omega
    have first : t.mem (off (curBuf s i).src k) = s.mem (off (curBuf s i).src k) := by
      rcases pre.source i hi with same | apart
      · rw [cur.firstMem same.1]
      · exact cur.frame.bytes apart (by change (curBuf s i).len ≤ _; omega) hk
    have last := cur.frame.bytes (pre.apart _ (show stream s ∈ [descR s,stream s] by simp)) (Nat.le_of_lt lt)
      (show j < total s by omega)
    rw [List.getElem?_append_right (by omega),hl, ← List.getD_eq_getElem?_getD]
    change _ = (Spec.Aes.bytesAt s.mem (curBuf s i).src (curBuf s i).len).getD k 0 ^^^ _
    rw [Proof.Gcm.getD_bytesAt' _ _ hk]
    have curByte := new k hk
    simp only [Buffers.byte,curBuf,off,Offset.add_add,e] at curByte
    exact curByte.trans (congr (congrArg (fun v : Byte => fun w : Byte => v ^^^ w) first) last)

abbrev countDown : List Instr := [.subImm .x .x7 .x7 1]

theorem body_ok {s i t} (pre : LoopPre s) (hi : i < num s) (c : AtDesc s i t) :
    WP isa (.seq shortPiece (.block countDown)) t (AtDesc s (i+1)) := by
  refine WP.seq ((shortPiece_ok (piecePre pre hi c)).mono fun u piece => ?_)
  have pD := extendOutput pre hi c piece _ (Or.inl rfl) c.outD piece.written.dst
  have pG := extendOutput pre hi c piece _ (Or.inr rfl) c.outG piece.written.auth
  have hgl : gl s i + (curBuf s i).len = gl s (i+1) := (gl_succ _ _ _).symm
  have descEq : u.gpr .x6 = off (ds s) (16*(i+1)) := by
    rw [piece.desc,c.desc]; simp only [off,show (16 : Addr) = BitVec.ofNat 64 16 from rfl,Offset.add_add,
      Nat.mul_add,Nat.mul_one]
  have cntEq : u.gpr .x7 - 1 = BitVec.ofNat 64 (num s-(i+1)) := by
    rw [piece.gpr _ (by decide),c.count,show (1:Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega),Nat.sub_sub]
  apply WP.of_runBlock
  simp only [countDown,runBlock_cons,runStep_some,runBlock_nil,exec,Nat.reduceLT,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨⟨fun r hr => ?_,piece.sp.trans c.sp,piece.rd.trans c.rd,piece.wr.trans c.wr⟩,
    descEq, cntEq, ?_,?_,?_,c.frame.trans (piece.written.frame.sub (curSub hi)), pD,pG,fun hzero => False.elim (by omega)⟩
  · have h7 : r ≠ .x7 := fun h => hr (by simp [loopRegs,h])
    exact (gpr_write_of_ne _ _ _ h7).trans ((piece.gpr r fun he => hr (List.mem_cons_of_mem _ he)).trans (c.gpr r hr))
  · change u.gpr .x1 = _
    rw [piece.ptrs.key]; change off (off _ _) _ = _; rw [off,off,Offset.add_add,hgl]
  · change u.gpr .x2 = _
    rw [piece.ptrs.dst]; change off (off _ _) _ = _; rw [off,off,Offset.add_add,hgl]
  · change u.gpr .x3 = _
    rw [piece.ptrs.auth]; change off (off _ _) _ = _; rw [off,off,Offset.add_add,hgl]

/-- The descriptor loop, including the zero-descriptor case. -/
theorem shortLoop_ok (s : State) (pre : LoopPre s) :
    WP isa (.ite (.zero .x .x7) (.block []) (.loop (.seq shortPiece (.block countDown)) (.nonzero .x .x7))) s
      (AtDesc s (num s)) := by
  have hn : s.gpr .x7 = BitVec.ofNat 64 (num s) := by simp [num]
  refine WP.ite _ (eval_zero hn (s.gpr .x7).isLt) (fun z => ?_) (fun nz => ?_)
  · exact WP.block_nil (by simpa only [of_decide_eq_true z] using AtDesc.init s)
  · have pos := of_decide_eq_false nz
    refine WP.loop (M := isa) (body := .seq shortPiece (.block countDown)) (c := .nonzero .x .x7)
      (fun k t => ∃ i, k = num s-i ∧ i < num s ∧ AtDesc s i t) ?_ (num s) s ⟨0, by simp,by omega,AtDesc.init s⟩
    rintro k t ⟨i,rfl,hi,cur⟩
    refine (body_ok pre hi cur).mono fun u step => ?_
    have lt := (s.gpr .x7).isLt
    change num s < 2 ^ 64 at lt
    have ev := eval_nonzero step.count (by omega)
    by_cases last : i+1 = num s
    · exact .inl ⟨by rw [ev,last]; simp,by simpa only [last] using step⟩
    · exact .inr ⟨by rw [ev]; simp [show num s - (i+1) ≠ 0 by omega],num s-(i+1),by omega,
        i+1,rfl,by omega,step⟩

/-- When the key buffer holds consecutive counter-mode bytes, both outputs
of the descriptor loop equal GCTR of the concatenation in the gather spec. -/
theorem AtDesc.gctr {s t : State} {i : Nat} (h : AtDesc s i t) (cipher : Spec.Gcm.Block → Spec.Gcm.Block)
    (icb : Spec.Gcm.Block)
    (ks : ∀ j < gl s i, s.mem (off (s.gpr .x1) j) = Proof.Gcm.ksByte cipher icb j) :
    Spec.Aes.bytesAt t.mem (s.gpr .x2) (gl s i) = Spec.Gcm.gctr cipher icb (pt s i) ∧
    Spec.Aes.bytesAt t.mem (s.gpr .x3) (gl s i) = Spec.Gcm.gctr cipher icb (pt s i) := by
  have hl := Proof.Gcm.length_gathered 64 s.mem (ds s) i
  change (pt s i).length = gl s i at hl
  rw [Proof.Gcm.gctr_eq]
  constructor <;>
    refine Proof.Gcm.list_ext (by rw [Proof.Gcm.length_xorKs,hl,Proof.Cmac.bytesAt_length]) fun j hj => ?_ <;>
    rw [Proof.Cmac.bytesAt_length] at hj <;>
    rw [Proof.Gcm.getD_bytesAt' _ _ hj,Proof.Gcm.getD_xorKs _ _ _ _ (hl ▸ hj),Nat.zero_add,← ks _ hj]
  · exact h.outD j hj
  · exact h.outG j hj

end VG.Proof.AesGcm.AArch64.DirectGather.Fragment
