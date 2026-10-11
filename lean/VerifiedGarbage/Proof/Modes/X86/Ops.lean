import VerifiedGarbage.Impl.Modes.X86.Seq
import VerifiedGarbage.Proof.Modes.Ops
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The modes' operations on x86 (32-bit)

`opsCode_wp`: the code of a list of operations (`Core.opsCode`) does to
the bytes of the three areas in memory what `applyOps` says (with the
areas' contents read from memory, `cont`), and changes nothing else in
memory, and no register but `eax` and `ecx`. It needs each area's address
(`AreasOk.ea`: the base register and displacement of the area give the
address `A l` plus the offset, without wrapping around), writable bytes,
and areas apart from each other.
-/

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Modes VG.Impl.Modes.X86

/-- The areas' contents, from memory: byte `i` of area `l` at `A l + i`. -/
def cont (A : Loc → Addr) (m : Mem) : Areas := fun l i => m (A l + BitVec.ofNat 64 i)

/-- The areas of the step, of lengths `len`, at `A` in `s`: each operand's
address, writable, and apart. -/
structure AreasOk (c : Core) (s : State) (len : Loc → Nat) (A : Loc → Addr) (ws : List Loc) : Prop where
  ea : ∀ l off, off < len l → addr (s.gpr (c.loc l).1) ((c.loc l).2 + off) = A l + BitVec.ofNat 64 off
  rd : ∀ l off w, off + w ≤ len l → InRegions (s.rd ++ s.wr) (A l + BitVec.ofNat 64 off) w
  wr : ∀ l ∈ ws, ∀ off w, off + w ≤ len l → InRegions s.wr (A l + BitVec.ofNat 64 off) w
  apart : ∀ l l', l ≠ l' → Region.Disjoint ⟨A l, len l⟩ ⟨A l', len l'⟩
  fit : ∀ l, len l < 2 ^ 32

theorem AreasOk.congr {c : Core} {s s' : State} {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc}
    (h : AreasOk c s len A ws) (hg : ∀ l, s'.gpr (c.loc l).1 = s.gpr (c.loc l).1) (hr : s'.rd = s.rd)
    (hw : s'.wr = s.wr) : AreasOk c s' len A ws :=
  ⟨fun l off ho => by rw [hg l]; exact h.ea l off ho, fun l off w ho => by rw [hr, hw]; exact h.rd l off w ho,
    fun l hl off w ho => by rw [hw]; exact h.wr l hl off w ho, h.apart, h.fit⟩

/-- Every area. -/
def allLocs : List Loc := [.dat, .chn, .buf]

theorem mem_allLocs (l : Loc) : l ∈ allLocs := by cases l <;> simp [allLocs]

/-- Memory after `o`: its destination's bytes are `Op.val` of the areas. -/
def opMem (A : Loc → Addr) (o : Op) (m : Mem) : Mem := fun x =>
  if (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat < o.width then
    o.val (cont A m) (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat
  else m x

/-! ## One instruction -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, byte [b + o]` -/
theorem wp_movzx {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 1)
    (k : ∀ s', Upd s s' d ((s.mem (addr B o)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, State.load8, ea_mk, hb, hin]) (k _ (Upd.setReg _ _ _))

/-- `mov byte [b + o], r8` -/
theorem wp_st8 {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

end

/-! ## Bytes of words -/

theorem write4_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  simp only [Mem.writeW, Mem.write]
  rfl

theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    m.writeW a v x = if (x - a).toNat < 1 then v else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · rename_i h
    rw [show (x - a).toNat = 0 by omega]
    simp
  · rfl

theorem byte_xor (u v : BitVec 32) (t : Nat) :
    (u ^^^ v).extractLsb' (8 * t) 8 = u.extractLsb' (8 * t) 8 ^^^ v.extractLsb' (8 * t) 8 := by
  ext j hj
  simp

theorem setWidth_xor8 (u v : Byte) : (u.setWidth 32 ^^^ v.setWidth 32).setWidth 8 = u ^^^ v := by
  ext j hj
  simp

theorem setWidth8_32 (u : Byte) : (u.setWidth 32).setWidth 8 = u := by
  ext j hj
  simp

theorem width_pos (o : Op) : 0 < o.width := by unfold Op.width; split <;> decide

theorem loc_ne (c : Core) (l : Loc) : (c.loc l).1 ≠ .eax ∧ (c.loc l).1 ≠ .ecx := by
  cases l <;> simp [Core.loc, sb]

/-! ## One operation -/

theorem opCode_wp (c : Core) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op} (ho : o.InBounds len)
    (hdst : o.dst ∈ ws) {s : State} (h : AreasOk c s len A ws) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = opMem A o s.mem → (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (c.opCode o ++ is)) s Q := by
  obtain ⟨hd, hs, hx⟩ := ho
  have hw0 := width_pos o
  -- Each base register, through writes of `eax` and `ecx`.
  have keep : ∀ {t : State}, (∀ r, r ≠ .eax → r ≠ .ecx → t.gpr r = s.gpr r) → ∀ l,
      t.gpr (c.loc l).1 = s.gpr (c.loc l).1 := fun ht l => ht _ (loc_ne c l).1 (loc_ne c l).2
  have eaD := h.ea o.dst o.dOff (by omega)
  have eaS := h.ea o.src o.sOff (by omega)
  unfold Core.opCode Core.opAt
  cases hwd : o.wide
  · -- A byte.
    have hW : o.width = 1 := by simp [Op.width, hwd]
    rw [hW] at hd hs hx
    simp only [Bool.false_eq_true, ite_false]
    cases hxr : o.xr with
    | none =>
      simp only [List.nil_append, List.cons_append]
      refine wp_movzx rfl (by rw [eaS]; exact h.rd _ _ _ hs) fun s₁ u₁ => ?_
      refine wp_st8 (keep (fun r h1 _ => u₁.other r h1) o.dst)
        (by rw [u₁.wr, eaD]; exact h.wr _ hdst _ _ hd) fun s₂ u₂ => ?_
      refine k s₂ ?_ (fun r h1 _ => by rw [u₂.gpr, u₁.other r h1]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      funext x
      rw [u₂.mem, u₁.mem, show Reg8.al.reg = Reg.eax from rfl, u₁.gpr, setWidth8_32, eaD, eaS, write1_apply]
      simp only [opMem, hW, Op.val, hxr, cont, byte_xor_zero]
      split
      · rename_i hlt; rw [show (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat = 0 by omega, Nat.add_zero]
      · rfl
    | some p =>
      obtain ⟨l, off⟩ := p
      have hx' := hx l off hxr
      have eaX := h.ea l off (by omega)
      simp only [List.cons_append]
      refine wp_movzx rfl (by rw [eaS]; exact h.rd _ _ _ hs) fun s₁ u₁ => ?_
      refine wp_movzx (keep (fun r h1 _ => u₁.other r h1) l)
        (by rw [u₁.rd, u₁.wr, eaX]; exact h.rd _ _ _ hx') fun s₂ u₂ => ?_
      refine wp_xor fun s₃ u₃ => ?_
      refine wp_st8 (keep (fun r h1 h2 => by rw [u₃.other r h1, u₂.other r h2, u₁.other r h1]) o.dst)
        (by rw [u₃.wr, u₂.wr, u₁.wr, eaD]; exact h.wr _ hdst _ _ hd) fun s₄ u₄ => ?_
      refine k s₄ ?_ (fun r h1 h2 => by rw [u₄.gpr, u₃.other r h1, u₂.other r h2, u₁.other r h1])
        (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      funext x
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      show (s.mem.writeW _ ((s₃.gpr Reg8.al.reg).setWidth 8)) x = _
      rw [show Reg8.al.reg = .eax from rfl, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, setWidth_xor8,
        eaD, eaS, eaX, write1_apply]
      simp only [opMem, hW, Op.val, hxr, cont]
      split
      · rename_i hlt; rw [show (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat = 0 by omega, Nat.add_zero,
          Nat.add_zero]
      · rfl
  · -- A word.
    have hW : o.width = 4 := by simp [Op.width, hwd]
    rw [hW] at hd hs hx
    simp only [ite_true]
    cases hxr : o.xr with
    | none =>
      simp only [List.nil_append, List.cons_append]
      refine wp_ldm rfl (by rw [eaS]; exact h.rd _ _ _ hs) fun s₁ u₁ => ?_
      refine wp_stm (keep (fun r h1 _ => u₁.other r h1) o.dst)
        (by rw [u₁.wr, eaD]; exact h.wr _ hdst _ _ hd) fun s₂ u₂ => ?_
      refine k s₂ ?_ (fun r h1 _ => by rw [u₂.gpr, u₁.other r h1]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      funext x
      rw [u₂.mem, u₁.mem, u₁.gpr, eaD, eaS, write4_apply]
      simp only [opMem, hW, Op.val, hxr, cont, byte_xor_zero]
      split
      · rename_i hlt; rw [← Mem.readW_byte s.mem _ hlt, VG.Offset.add_add]
      · rfl
    | some p =>
      obtain ⟨l, off⟩ := p
      have hx' := hx l off hxr
      have eaX := h.ea l off (by omega)
      simp only [List.cons_append]
      refine wp_ldm rfl (by rw [eaS]; exact h.rd _ _ _ hs) fun s₁ u₁ => ?_
      refine wp_xorm (keep (fun r h1 _ => u₁.other r h1) l)
        (by rw [u₁.rd, u₁.wr, eaX]; exact h.rd _ _ _ hx') fun s₂ u₂ => ?_
      refine wp_stm (keep (fun r h1 _ => by rw [u₂.other r h1, u₁.other r h1]) o.dst)
        (by rw [u₂.wr, u₁.wr, eaD]; exact h.wr _ hdst _ _ hd) fun s₃ u₃ => ?_
      refine k s₃ ?_ (fun r h1 _ => by rw [u₃.gpr, u₂.other r h1, u₁.other r h1])
        (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
      funext x
      rw [u₃.mem, u₂.mem, u₂.gpr, u₁.mem, u₁.gpr, eaD, eaS, eaX, write4_apply]
      simp only [opMem, hW, Op.val, hxr, cont]
      split
      · rename_i hlt; rw [byte_xor, ← Mem.readW_byte s.mem _ hlt, ← Mem.readW_byte s.mem _ hlt, VG.Offset.add_add,
          VG.Offset.add_add]
      · rfl

/-! ## Areas -/

/-- The regions of the areas `ws`. -/
def areaRegions (len : Loc → Nat) (A : Loc → Addr) (ws : List Loc) : List Region :=
  ws.map fun l => ⟨A l, len l⟩

theorem sub_self_add (p : Addr) {i : Nat} (hi : i < 2 ^ 64) : (p + BitVec.ofNat 64 i - p).toNat = i := by
  rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem contains_area {p : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := by
  simp only [Region.Contains]; rw [sub_self_add p (by omega)]; omega

/-- A byte the destination of `o` writes is in its area. -/
theorem in_dst {len : Loc → Nat} {A : Loc → Addr} {o : Op} (ho : o.InBounds len) (hfit : len o.dst < 2 ^ 32)
    {x : Addr} (hx : (x - (A o.dst + BitVec.ofNat 64 o.dOff)).toNat < o.width) :
    (⟨A o.dst, len o.dst⟩ : Region).Contains x 1 := by
  have hw : o.width ≤ 4 := by unfold Op.width; split <;> decide
  have := (VG.Offset.lt_iff x (A o.dst) (d := o.dOff) (n := o.width) (by have := ho.1; omega)).mp hx
  simp only [Region.Contains]; have := ho.1; omega

theorem opMem_frame {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {o : Op} (ho : o.InBounds len)
    (hdst : o.dst ∈ ws) (hfit : ∀ l, len l < 2 ^ 32) (m : Mem) : Frame (areaRegions len A ws) m (opMem A o m) := by
  intro x hx
  simp only [opMem]
  rw [ite_eq_right fun h => hx _ (List.mem_map.mpr ⟨_, hdst, rfl⟩) (in_dst ho (hfit _) h)]

theorem opMem_cont {c : Core} {s : State} {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc}
    (h : AreasOk c s len A ws) {o : Op}
    (ho : o.InBounds len) (m : Mem) : Agree len (cont A (opMem A o m)) (o.apply (cont A m)) := by
  intro l i hi
  have hl := h.fit l
  simp only [cont, opMem, Op.apply]
  by_cases hd : l = o.dst
  · subst hd
    have e := VG.Offset.lt_iff (A o.dst + BitVec.ofNat 64 i) (A o.dst) (d := o.dOff) (n := o.width)
      (by have := ho.1; omega)
    rw [sub_self_add _ (by omega)] at e
    by_cases hc : o.dOff ≤ i ∧ i < o.dOff + o.width
    · rw [ite_eq_left (e.mpr hc), ite_eq_left ⟨rfl, hc⟩]
      congr 1
      rw [← VG.Offset.add_add_eq (A o.dst) (Nat.add_sub_cancel' hc.1), sub_self_add _ (by omega)]
    · rw [ite_eq_right (fun h' => hc (e.mp h')), ite_eq_right (fun h' => hc h'.2)]
  · rw [ite_eq_right (fun h' => h.apart l o.dst hd _ (contains_area hi (by omega)) (in_dst ho (h.fit _) h')),
      ite_eq_right (fun h' => hd h'.1)]

/-! ## Lists of operations -/

theorem opsCode_wp (c : Core) {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} :
    ∀ {os : List Op}, (∀ o ∈ os, o.InBounds len ∧ o.dst ∈ ws) → ∀ {s : State}, AreasOk c s len A ws →
    ∀ {is : List Instr} {Q : State → Prop},
    (∀ s', Agree len (cont A s'.mem) (applyOps os (cont A s.mem)) → Frame (areaRegions len A ws) s.mem s'.mem →
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) →
    WP isa (.block (c.opsCode os ++ is)) s Q
  | [], _, s, _, is, Q, k => by
    simpa [Core.opsCode] using k s (fun _ _ _ => rfl) (Frame.refl _ _) (fun _ _ _ => rfl) rfl rfl
  | o :: os, hb, s, h, is, Q, k => by
    have ho := (hb o List.mem_cons_self).1
    rw [show c.opsCode (o :: os) ++ is = c.opCode o ++ (c.opsCode os ++ is) by
      simp [Core.opsCode, List.append_assoc]]
    refine opCode_wp c ho (hb o List.mem_cons_self).2 h fun s₁ m₁ g₁ rd₁ wr₁ => ?_
    have h₁ : AreasOk c s₁ len A ws := h.congr (fun l => g₁ _ (loc_ne c l).1 (loc_ne c l).2) rd₁ wr₁
    refine opsCode_wp c (fun o' ho' => hb o' (List.mem_cons_of_mem _ ho')) h₁ fun s' a' f' g' rd' wr' => ?_
    refine k s' (fun l i hi => ?_) ?_ (fun r h1 h2 => by rw [g' r h1 h2, g₁ r h1 h2]) (by rw [rd', rd₁])
      (by rw [wr', wr₁])
    · rw [a' l i hi, applyOps_cons]
      refine applyOps_agree (fun o' ho' => (hb o' (List.mem_cons_of_mem _ ho')).1) (fun l' i' hi' => ?_) l i hi
      rw [m₁]; exact opMem_cont h ho _ l' i' hi'
    · rw [m₁] at f'; exact (opMem_frame ho (hb o List.mem_cons_self).2 h.fit _).trans f'

end VG.Proof.Modes.X86
