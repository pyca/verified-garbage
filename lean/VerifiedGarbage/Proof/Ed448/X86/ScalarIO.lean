import VerifiedGarbage.Proof.Ed448.X86.ScalarLoop
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Output

/-!
# Ed448 scalar arithmetic on x86 (32-bit): entry and exit

The cdecl arguments (`Args`: they stay on the stack, which the code does not
write, `Args.load`), the callee-saved registers saved in the working space
(`save_ok`, as X448 saves them), the remainders of the inputs
(`reduce114_ok`, `reduce57_ok`), and the result: the remainder's limbs as 56
bytes and a zero byte, its encoding, then the registers restored
(`finish_ok`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR zeroR reduce114 reduce57 packLimb finish)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-! ## The arguments -/

/-- The `n` cdecl arguments of 4 bytes on the stack, readable and disjoint
from the working space, the argument `sc`. -/
structure Args (s₀ : State) (n sc : Nat) : Prop where
  in_rd : (⟨argAddr s₀ 0, 4 * n⟩ : Region) ∈ s₀.rd
  sp_fit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  sc_lt : sc < n
  sc_in : scR (arg s₀ sc) ∈ s₀.wr
  sc_fit : (arg s₀ sc).toNat + 8192 ≤ 2 ^ 32
  args_sc : (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint (scR (arg s₀ sc))
  ret_sc : (retR s₀).Disjoint (scR (arg s₀ sc))

namespace Args
variable {s₀ : State} {n sc : Nat} (hp : Args s₀ n sc)
include hp

theorem arg_contains {i : Nat} (hi : i < n) :
    (⟨argAddr s₀ 0, 4 * n⟩ : Region).Contains (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.X25519.X86.sub_contains (x := s₀.gpr .esp) (a := 4) (k := 4 * n)
    (by have := hp.sp_fit; omega) (by omega) (by omega) (by decide)

/-- An argument, in memory the code has written only in the working space. -/
theorem arg_same {m : Mem} (hf : Frame [scR (arg s₀ sc)] s₀.mem m) {i : Nat} (hi : i < n) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (hp.arg_contains hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

theorem load {s : State} (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd)
    (hw : s.wr = s₀.wr) (hm : Outside ((arg s₀ sc).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < n) {d : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t d (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem (Impl.X448.X86.at_ .esp (4 + 4 * i))) :: is)) s Q := by
  refine wp_load (a := addr (s₀.gpr .esp) (4 + 4 * i))
    (by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp])
    (by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩) fun t ht => ?_
  rw [hp.arg_same hm.frame hi] at ht
  exact k t ht

end Args

/-! ## Saving the callee-saved registers -/

theorem save_ok {s : State} {n sc : Nat} (hp : Args s n sc) :
    WP isa (.block (Impl.Ed448.X86.save (4 + 4 * sc))) s fun t =>
      Scr t ((arg s sc).setWidth 64) ∧ Saved ((arg s sc).setWidth 64) s.gpr t.mem ∧
      Outside ((arg s sc).setWidth 64) 0 16 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (Impl.X448.X86.at_ .esp (4 + 4 * sc))) ::
    (Spill.saveCode .eax savedSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine hp.load rfl rfl rfl (Outside.refl _ _ _ _) hp.sc_lt fun t ht => ?_
  have hfit := hp.sc_fit
  refine Spill.save_ofNat_ok savedSlots (n := 16) (by decide) (by rw [ht.gpr]; omega)
    (fun p h => by rw [ht.gpr, ht.wr]; exact ⟨_, hp.sc_in, contains_sc (by have := savedSlots_bound p h; omega)⟩)
    fun u hu => ?_
  have hm : u.mem = Spill.saveMem s.mem (off ((arg s sc).setWidth 64)) s.gpr savedSlots := by
    rw [hu.mem, ht.gpr, ht.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => ht.other _ (by revert p h; decide)
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (ht.rest (by decide)).trans
    (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : Keeps [.eax, .edi] t u) |>.trans (hv.rest (by decide))⟩
  · rw [hv.gpr, hu.gpr, ht.gpr]
  · rw [hv.wr, hu.wr, ht.wr]; exact hp.sc_in
  · rw [hv.gpr, hu.gpr, ht.gpr]; exact hfit
  · rw [hv.mem, hm]; exact Spill.saveMem_saved_ofNat _ _ _ (n := 16) (by decide) (by decide)
  · rw [hv.mem, hm]
    exact Outside.of_frame (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      Offset.contains_base _ (savedSlots_bound p h) (by have := savedSlots_bound p h; omega))

/-! ## The remainders of the inputs -/

theorem init114_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (zeroR o ++ ([.mov .ebp (.imm 114)] : List Instr))) s fun v =>
      LoopKeep base o s v ∧ v.gpr .ebp = BitVec.ofNat 32 114 ∧ Bounded v.mem base o ∧
        fe v.mem base o = 0 := by
  rw [WP.block_append_iff]
  refine WP.mono (zeroR_ok ho.2 hs) fun u ⟨ku, fu, zu⟩ =>
    wp_mov rfl fun v hv => WP.block_nil
      ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by
        rw [hv.mem]; exact fun p _ h2 => fu p h2⟩,
        hv.gpr, by rw [hv.mem]; exact Bounded_zero zu, by rw [hv.mem]; exact fe_zero zu⟩

/-- The input's bytes, readable and beyond the working space. -/
structure Input (s : State) (base : Addr) (p : BitVec 32) (N : Nat) : Prop where
  fit : p.toNat + N ≤ 2 ^ 32
  read : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1
  far : ∀ i < N, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 i)

theorem Input.of_keeps {s t : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N)
    {rs : List Reg} (hk : Keeps rs s t) : Input t base p N :=
  ⟨h.fit, by rw [hk.2.1, hk.2.2]; exact h.read, h.far⟩

/-- An input's bytes across a change of the working space. -/
theorem Input.bytes {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N)
    {m m' : Mem} (hm : Outside base 0 8192 m m') :
    bytesAt m' (p.setWidth 64) N = bytesAt m (p.setWidth 64) N := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => hm _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact h.far i hi

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega)
    (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

/-- The working space lies beyond a region of `n` bytes disjoint from it. -/
theorem far_out {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    {i : Nat} (hi : i < 8192) : n ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192)
    (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ n
  omega

theorem Input.of_region {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (hfit : p.toNat + N ≤ 2 ^ 32)
    (hin : (⟨p.setWidth 64, N⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : (⟨p.setWidth 64, N⟩ : Region).Disjoint ⟨base, 8192⟩) : Input s base p N :=
  ⟨hfit, fun i hi => ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => VG.Proof.Ed448.X86.far hd hi (by omega)⟩

theorem LoopKeep.whole {base : Addr} {o : Nat} {s t : State} (h : LoopKeep base o s t)
    (ho : o + 112 ≤ 8192) : Outside base 0 8192 s.mem t.mem :=
  fun p hp => h.mem p (by simp only [W]; omega) (by omega)

theorem reduce114_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 114) :
    WP isa (reduce114 o) s fun t => LoopKeep base o s t ∧ Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s.mem (p.setWidth 64) 114) % L := by
  unfold reduce114
  refine WP.seq (WP.mono (init114_ok ho hs) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := hin.bytes (kv.whole (by have := ho.2; omega))
  refine WP.mono (byteLoop_ok (N := 114) ho (hs.of_keeps kv.regs (by decide))
    ((kv.regs.1 _ (by decide)).trans hp) hin.fit (by rw [kv.regs.2.1, kv.regs.2.2]; exact hin.read)
    hin.far (n0 := 114) (by decide) (by decide) (by decide) cv lv
    (by rw [vv, List.drop_eq_nil_of_le (by rw [Proof.Ed448.bytesAt_length]),
      show decodeLE [] = 0 from rfl, Nat.zero_mod]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

theorem init57_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 57) :
    WP isa (.block (zeroR o ++ ([.movzx8 .eax (Impl.X448.X86.at_ .esi 56), Impl.X448.X86.st .eax o,
      .mov .ebp (.imm 56)] : List Instr))) s fun v =>
      LoopKeep base o s v ∧ v.gpr .ebp = BitVec.ofNat 32 56 ∧ Bounded v.mem base o ∧
      fe v.mem base o = decodeLE ((bytesAt s.mem (p.setWidth 64) 57).drop 56) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  rw [WP.block_append_iff]
  refine WP.mono (zeroR_ok ho2 hs) fun u ⟨ku, fu, zu⟩ => ?_
  have hpu : u.gpr .esi = p := (ku.1 _ (by decide)).trans hp
  have hsu := hs.of_keeps ku (by decide)
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 56)
    (by change addr (u.gpr .esi) 56 = _; rw [hpu]; exact addr_eq (by have := hin.fit; omega))
    (by rw [ku.2.1, ku.2.2]; exact hin.read 56 (by decide)) fun u1 v1 => ?_
  refine store_ok (hsu.of_upd v1 (by decide)) (by omega) fun u2 v2 => wp_mov rfl fun v hv =>
    WP.block_nil ?_
  have byte : u.mem (p.setWidth 64 + BitVec.ofNat 64 56) = s.mem (p.setWidth 64 + BitVec.ofNat 64 56) :=
    fu _ (Or.inr (by have := hin.far 56 (by decide); omega))
  have m2 : v.mem = u.mem.writeW (off base (o + 4 * 0))
      ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).setWidth 32) := by
    rw [hv.mem, v2.mem, v1.gpr, v1.mem, byte]; rfl
  have lv : ∀ k < 28, limbs v.mem base o k =
      if k = 0 then (s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat else 0 := by
    intro k hk
    change (word v.mem base (o + 4 * k)).toNat = _
    rw [m2, word_write u.mem base (by omega) (by omega)]
    by_cases k0 : k = 0
    · rw [ite_eq_left k0, ite_eq_left k0, BitVec.toNat_setWidth_of_le (by decide)]
    · rw [ite_eq_right k0, ite_eq_right k0]; exact zu k hk
  have hlt := (s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).isLt
  refine ⟨⟨(ku.mono (by decide)).trans ((v1.rest (by decide)).trans ((v2.rest _).trans
    (hv.rest (by decide)))), ?_⟩, hv.gpr, fun k hk => ?_, ?_⟩
  · rw [m2]
    intro q _ h2
    rw [writeW_outside _ _ _ (by omega) q (by omega)]
    exact fu q h2
  · rw [lv k hk]; split
    · simp only [radix]; omega
    · decide
  · rw [decode_drop1 _ _ (by decide : 56 + 1 = 57)]
    have hL : 256 < L := by decide +kernel
    rw [Nat.mod_eq_of_lt (by omega)]
    show valN (limbs v.mem base o) 28 = _
    rw [show (28 : Nat) = 1 + 27 from rfl, valN_split,
      valN_congr (n := 27) (g := fun _ => 0) (fun k hk => by rw [lv _ (by omega), ite_eq_right (by omega)]),
      valN_zero]
    simp only [valN, lv 0 (by decide), ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.add_zero]

theorem reduce57_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 57) :
    WP isa (reduce57 o) s fun t => LoopKeep base o s t ∧ Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s.mem (p.setWidth 64) 57) % L := by
  unfold reduce57
  refine WP.seq (WP.mono (init57_ok ho hs hp hin) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := hin.bytes (kv.whole (by have := ho.2; omega))
  refine WP.mono (byteLoop_ok (N := 57) ho (hs.of_keeps kv.regs (by decide))
    ((kv.regs.1 _ (by decide)).trans hp) hin.fit (by rw [kv.regs.2.1, kv.regs.2.2]; exact hin.read)
    hin.far (n0 := 56) (by decide) (by decide) (by decide) cv lv (by rw [vv, mb]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

/-! ## The result -/

/-- Writes to the output preserve a word of the disjoint working space. -/
theorem out_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m')
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, n ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (by have := hfar (d + i) (by omega); simp only [off] at this; omega))

theorem packLimb_ok {s : State} {base p : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o) {i : Nat} (hi : i < 28) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (off p (2 * i + j)) 1) :
    WP isa (.block (packLimb o i)) s fun t =>
      decoded t.mem p i = limbs s.mem base o i ∧ Outside p (2 * i) 2 s.mem t.mem ∧ Keeps [.eax] s t := by
  have ea : ∀ j < 2, addr (s.gpr .esi) (2 * i + j) = off p (2 * i + j) := by
    intro j hj; rw [addr_eq (by omega), hp]
  unfold packLimb
  refine load_ok hs (by omega) fun t ht => ?_
  refine wp_store8 (a := off p (2 * i))
    (by change addr (t.gpr .esi) _ = _; rw [ht.other .esi (by decide)]; exact ea 0 (by decide))
    (by rw [ht.wr]; exact hw 0 (by decide)) fun u hu => ?_
  refine wp_shift (by decide) fun v hv => ?_
  refine wp_store8 (a := off p (2 * i + 1))
    (by change addr (v.gpr .esi) _ = _
        rw [hv.other .esi (by decide), hu.gpr, ht.other .esi (by decide)]; exact ea 1 (by decide))
    (by rw [hv.wr, hu.wr, ht.wr]; exact hw 1 (by decide)) fun w hw' => WP.block_nil ⟨?_, ?_, ?_⟩
  · have hm : w.mem = packMem s.mem p i (word s.mem base (o + 4 * i)) := by
      rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
    rw [hm]; exact packMem_decoded _ _ hi _ (hb i hi)
  · have hm : w.mem = packMem s.mem p i (word s.mem base (o + 4 * i)) := by
      rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
    rw [hm]; exact packMem_outside _ _ hi _
  · exact ((ht.rest (by decide)).trans ((hu.rest _).trans
      ((hv.rest (by decide)).trans (hw'.rest _))))

theorem packAll_ok {s : State} {base p : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 57 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 28).flatMap (packLimb o))) s fun t =>
      (∀ i < 28, decoded t.mem p i = limbs s.mem base o i) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, decoded t.mem p i = limbs s.mem base o i) ∧ Outside p 0 (2 * n) s.mem t.mem ∧
      Keeps [.eax] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (packLimb o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 28, limbs t.mem base o j = limbs s.mem base o j := by
      intro j hj
      exact congrArg BitVec.toNat (out_word tm (by omega) fun i hi => Nat.le_trans (by omega) (hfar i hi))
    have tb : Bounded t.mem base o := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (packLimb_ok (p := p) (hs.of_keeps tk (by decide)) ho tb hn
      (by rw [tk.1 _ (by decide)]; exact hp) (by rw [tk.1 _ (by decide)]; exact hfit)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega))) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, (tm.mono (by decide) (by omega)).trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans (eq n hn)
    · have byte : ∀ j < 2, u.mem (off p (2 * i + j)) = t.mem (off p (2 * i + j)) := by
        intro j hj
        exact um _ (Or.inl (by rw [ofs_off' p (by omega)]; omega))
      simp only [decoded, byteN]
      have b0 := byte 0 (by decide)
      have b1 := byte 1 (by decide)
      simp only [off, Nat.add_zero] at b0 b1
      rw [b0, b1]
      exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The registers `finish` changes. -/
def finishRegs : List Reg := [.eax, .ebx, .esi, .edi, .ebp]

/-- `finish o`: the remainder at `o` as 57 bytes at the output (the argument
0), and the callee-saved registers restored. -/
theorem finish_ok {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (h0 : 0 < n)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ sc).setWidth 64 = base)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o)
    (hout : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region) ∈ s₀.wr) (hofit : (arg s₀ 0).toNat + 57 ≤ 2 ^ 32)
    (hfar : ∀ j < 8192, 57 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j))
    (sv : Saved base s₀.gpr s.mem) :
    WP isa (.block (finish o)) s fun t =>
      (∀ p ∈ savedSlots, t.gpr p.1 = s₀.gpr p.1) ∧ Keeps finishRegs s t ∧
      Outside ((arg s₀ 0).setWidth 64) 0 57 s.mem t.mem ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 = encodeLE 57 (fe s.mem base o) := by
  unfold finish
  simp only [List.cons_append, List.append_assoc]
  refine hp.load hsp hr hwr (hbase ▸ hm) h0 fun v hv => ?_
  generalize hP : (arg s₀ 0).setWidth 64 = P at hout hfar ⊢
  have hvs := hs.of_upd hv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (packAll_ok hvs ho (hv.mem ▸ hb) (by rw [hv.gpr, hP]) (by rw [hv.gpr]; exact hofit)
    (by intro j hj; rw [hv.wr, hwr]; exact ⟨_, hout, Offset.contains_base _ (by omega) (by omega)⟩)
    hfar) fun w ⟨wd, wm, wk⟩ => ?_
  refine wp_mov rfl fun x hx => ?_
  have hxs : x.gpr .esi = arg s₀ 0 := by
    rw [hx.other .esi (by decide), wk.1 _ (by decide), hv.gpr]
  refine wp_store8 (a := P + BitVec.ofNat 64 56)
    (by change addr (x.gpr .esi) 56 = _; rw [hxs, addr_eq (by omega), hP])
    (by rw [hx.wr, wk.2.2, hv.wr, hwr]; exact ⟨_, hout, Offset.contains_base _ (by decide) (by decide)⟩)
    fun y hy => ?_
  have hm2 : y.mem = w.mem.writeW (P + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [hy.mem, Reg8.reg, hx.gpr, hx.mem]; rfl
  have ym : Outside P 0 57 s.mem y.mem := by
    rw [hm2, ← hv.mem]
    intro q hq
    rw [writeW8_outside _ _ _ (by decide) (by intro e; simp only [ofs] at hq e; omega)]
    exact wm q (by omega)
  have ys := ((hvs.of_keeps wk (by decide)).of_upd hx (by decide)).of_keeps (hy.rest []) (by decide)
  have svy : Saved base s₀.gpr y.mem := sv.of_readW fun q hq => by
    have := savedSlots_bound q hq
    exact out_word ym (by omega) hfar
  refine WP.mono (restore_ok ys svy) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, ?_, by rw [tm]; exact ym, ?_⟩
  · refine (hv.rest (by decide)).trans ((wk.mono (by decide)).trans ((hx.rest (by decide)).trans
      ((hy.rest _).trans (tk.mono ?_))))
    intro r hr; simp only [restoreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [tm]
    refine encode_57 hb (fun k hk => ?_) ?_
    · have e := wd k hk
      rw [hv.mem] at e
      rw [← e]
      simp only [decoded, byteN]
      have b : ∀ i < 56, y.mem (P + BitVec.ofNat 64 i) = w.mem (P + BitVec.ofNat 64 i) := fun i hi => by
        rw [hm2, writeW8_outside _ _ _ (by decide) (by rw [ofs_off' P (by omega)]; omega)]
      rw [b (2 * k) (by omega), b (2 * k + 1) (by omega)]
    · rw [hm2, writeW8_apply, ite_eq_left rfl]

end VG.Proof.Ed448.X86
