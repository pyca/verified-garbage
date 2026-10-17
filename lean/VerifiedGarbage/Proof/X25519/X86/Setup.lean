module

public import VerifiedGarbage.Proof.X25519.X86.Step
import VerifiedGarbage.Proof.X25519.X86.Freeze
public import VerifiedGarbage.Proof.X25519.X86.Contract
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# X25519 on x86 (32-bit): reading the arguments

`save` stores the callee-saved registers in the working space, `loadPoint` the
u-coordinate (its top bit masked) in `X1`, `loadScalar` the bits of the scalar
in `BITS` (clamped), and `initLadder` the ladder's initial state; so the
ladder starts with `LInv 255`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem save_eq : save = .mov .eax (.mem (at_ .esp 16)) :: (Spill.saveCode .eax savedSlots ++
    ([.mov .edi (.reg .eax)] : List Instr)) := rfl

/-- What `save` leaves. -/
structure Saved (s₀ s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR 4096 (arg s₀ 3)] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr (arg s₀ 3)) s₀.gpr savedSlots

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (Saved s₀) := by
  have hfit := hp.sc_fit
  rw [save_eq]
  refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 16) rfl (hp.argIn (i := 3) (by decide)) fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = arg s₀ 3 := u₁.gpr
  have inW : ∀ {s : State} {d : Nat}, s.wr = s₀.wr → d + 4 ≤ 4096 → InRegions s.wr (addr (arg s₀ 3) d) 4 :=
    fun hw hd => ⟨_, hw ▸ hp.sc_in, scR_contains hfit hd (by decide)⟩
  refine Spill.save_ok savedSlots (fun p h => by
    rw [ea]; exact inW u₁.wr (by have := savedSlots_bound p h; omega_using [this])) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hr : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  have hm : s₆.mem = Spill.saveMem s₀.mem (addr (arg s₀ 3)) s₀.gpr savedSlots := by
    rw [u₆.mem, u₅.mem, ea, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => hr _ (by revert p h; decide)
  refine ⟨by rw [u₆.gpr, u₅.gpr, ea], by rw [u₆.other _ (by decide), u₅.gpr, hr _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₁.wr], ?_, ?_⟩
  · rw [hm]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      scR_contains hfit (by have := savedSlots_bound p h; omega_using [this]) (by decide)
  · rw [hm]; exact Spill.saveMem_saved_addr _ _ (n := 16) (by decide) (by omega_using [hfit])

/-- A store to the working space above the saved registers keeps `Saved`. -/
theorem Saved.write {s₀ s s' : State} (hp : Pre s₀) (h : Saved s₀ s) {d : Nat} (hd : 16 ≤ d)
    (hd' : d + 4 ≤ 4096) (hg : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {v : BitVec 32} (hm : s'.mem = s.mem.writeW (addr (arg s₀ 3) d) v) : Saved s₀ s' := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (scR_contains hfit hd' (by decide))
  · have := savedSlots_bound p hp
    rw [hm]
    exact wd_write_ne _ _ (by omega_using [hfit, this]) (by omega_using [hfit, hd']) (.inl (by omega_using [this, hd]))

/-- The words of the u-coordinate, on entry. -/
abbrev pw (s₀ : State) (k : Nat) : BitVec 32 := wd s₀.mem (arg s₀ 2) (4 * k)

/-- The words `X1` receives: those of the u-coordinate, the top bit masked. -/
def pv (s₀ : State) (k : Nat) : BitVec 32 := if k = 7 then pw s₀ 7 &&& low31 else pw s₀ k

/-- A word of the u-coordinate, unchanged. -/
theorem point_contains {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8) :
    (pointR s₀).Contains (addr (arg s₀ 2) (4 * k)) 4 := by
  have := sub_contains (x := arg s₀ 2) (a := 0) (k := 32) (d := 4 * k) (n := 4)
    (by have := hp.point_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)
  rwa [sub, addr_zero] at this

/-- A word of the u-coordinate, unchanged. -/
theorem Saved.pw {s₀ s : State} (hp : Pre s₀) (h : Saved s₀ s) {k : Nat} (hk : k < 8) :
    wd s.mem (arg s₀ 2) (4 * k) = pw s₀ k :=
  h.frame.readW (point_contains hp hk)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.point_sc) (by decide)

theorem loadWord_ok {s₀ s : State} (hp : Pre s₀) {n : Nat} (hn : n < 8)
    (h : Saved s₀ s) (hesi : s.gpr .esi = arg s₀ 2) (hw : ∀ j < n, wd s.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j) :
    WP isa (.block (([.mov .eax (.mem (at_ .esi (4 * n)))] : List Instr) ++
      (if n = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * n)) .eax] : List Instr))) s fun s' =>
      Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
  have hfit := hp.sc_fit
  have hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 2) (4 * n)) 4 :=
    ⟨pointR s₀, by rw [h.rd, hp.rd]; simp, point_contains hp hn⟩
  simp only [List.cons_append, List.nil_append]
  refine Wp.wp_ldm hesi hin fun s₁ u₁ => ?_
  -- The rest, from the value `w` in `eax`.
  have fin : ∀ (s₂ : State) (w : BitVec 32), s₂.gpr .eax = w → w = pv s₀ n → s₂.gpr .edi = s.gpr .edi →
      s₂.gpr .esp = s.gpr .esp → s₂.gpr .esi = s.gpr .esi → s₂.rd = s.rd → s₂.wr = s.wr → s₂.mem = s.mem →
      WP isa (.block [.store (sc (X1 + 4 * n)) .eax]) s₂ fun s' =>
        Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
    intro s₂ w ew hw' g1 g2 g3 g4 g5 g6
    refine Wp.wp_stm (by rw [g1]; exact h.edi) ⟨_, by rw [g5, h.wr]; exact hp.sc_in,
      scR_contains hfit (by simp only [X1]; omega_using [hn]) (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    refine ⟨h.write hp (d := X1 + 4 * n) (by simp only [X1]; omega_using []) (by simp only [X1]; omega_using [hn])
      (by rw [u₃.gpr, g1]) (by rw [u₃.gpr, g2]) (by rw [u₃.rd, g4]) (by rw [u₃.wr, g5]) (by rw [u₃.mem, g6]),
      by rw [u₃.gpr, g3, hesi], fun j hj => ?_⟩
    rw [u₃.mem, g6]
    by_cases e : j = n
    · subst e; rw [wd_write_self, ew, hw']
    · rw [wd_write_ne _ _ (by simp only [X1]; omega_using [hfit, hj, hn]) (by simp only [X1]; omega_using [hfit, hn])
        (by omega_using [e])]
      exact hw j (by omega_using [hj, e])
  have e₁ : s₁.gpr .eax = pw s₀ n := by rw [u₁.gpr]; exact h.pw hp hn
  by_cases h7 : n = 7
  · subst h7
    simp only [ite_true, List.cons_append, List.nil_append]
    refine Wp.wp_andi fun s₂ u₂ => fin s₂ _ u₂.gpr ?_ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem])
    rw [e₁]; rfl
  · simp only [h7, ite_false, List.nil_append]
    exact fin s₁ _ rfl (by rw [e₁, pv, ite_eq_right h7]) (u₁.other _ (by decide)) (u₁.other _ (by decide))
      (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.mem

theorem loadWords_ok {s₀ : State} (hp : Pre s₀) : ∀ n ≤ 8, ∀ s, Saved s₀ s → s.gpr .esi = arg s₀ 2 →
    WP isa (.block ((List.range n).flatMap fun k => ([.mov .eax (.mem (at_ .esi (4 * k)))] : List Instr) ++
      (if k = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * k)) .eax] : List Instr))) s fun s' =>
      Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j
  | 0, _, _, h, he => WP.block_nil ⟨h, he, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hn, s, h, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (loadWords_ok hp n (by omega_using [hn]) s h he) fun s₁ ⟨h₁, e₁, w₁⟩ =>
      loadWord_ok hp (by omega_using [hn]) h₁ e₁ w₁)

theorem loadPoint_ok {s₀ s : State} (hp : Pre s₀) (h : Saved s₀ s) :
    WP isa (.block loadPoint) s fun s' => Saved s₀ s' ∧ ∀ j < 8, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
  refine Wp.wp_ldm (B := s.gpr .esp) (o := 12) rfl (by rw [h.esp, h.rd, h.wr]; exact hp.argIn (i := 2) (by decide))
    fun s₁ u₁ => ?_
  have h₁ : Saved s₀ s₁ := ⟨by rw [u₁.other _ (by decide)]; exact h.edi, by rw [u₁.other _ (by decide)]; exact h.esp,
    by rw [u₁.rd]; exact h.rd, by rw [u₁.wr]; exact h.wr, by rw [u₁.mem]; exact h.frame,
    by rw [u₁.mem]; exact h.saved⟩
  have e₁ : s₁.gpr .esi = arg s₀ 2 := by
    rw [u₁.gpr, h.esp]; exact hp.arg_same h.frame (i := 2) (by decide)
  exact WP.mono (loadWords_ok hp 8 (Nat.le_refl _) s₁ h₁ e₁) fun s' ⟨h', _, w'⟩ => ⟨h', w'⟩

/-! ## The scalar's bits -/

theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Wp.Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, State.store8, ea_mk, ha, hout, ↓reduceIte]

theorem byte_write_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem byte_write_ne (m : Mem) {x : BitVec 32} (v : BitVec 8) {d e : Nat} (hd : x.toNat + d + 1 ≤ 2 ^ 32)
    (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) : (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  have hdisj := sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])

theorem Saved.of_frame {s₀ sA s : State} (hp : Pre s₀) (h : Saved s₀ sA) {o n : Nat}
    (hf : Frame [sub (arg s₀ 3) o n] sA.mem s.mem) (ho : 16 ≤ o) (hon : o + n ≤ 4096) (hn : o < 4096)
    (hg : s.gpr .edi = sA.gpr .edi) (hesp : s.gpr .esp = sA.gpr .esp) (hrd : s.rd = sA.rd) (hwr : s.wr = sA.wr) :
    Saved s₀ s := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr, scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hon]) hn⟩)
  · have := savedSlots_bound p hp
    exact wd_frame1 hf hfit hon (by omega_using [this]) (.inl (by omega_using [this, ho]))

/-- Byte `i` of the scalar, on entry. -/
abbrev sb (s₀ : State) (i : Nat) : Nat := (s₀.mem (addr (arg s₀ 1) i)).toNat

/-- The bits stored so far. -/
structure BInv (s₀ sA : State) (t : Nat) (s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esp : s.gpr .esp = sA.gpr .esp
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  frame : Frame [sub (arg s₀ 3) BITS 256] sA.mem s.mem
  bits : ∀ u < t, s.mem (addr (arg s₀ 3) (BITS + u)) = BitVec.ofNat 8 ((sb s₀ (u / 8) >>> (u % 8)) &&& 1)

/-- `BInv` through instructions that keep `edi`, `esp` and memory. -/
theorem BInv.upd {s₀ sA s s' : State} {t : Nat} (h : BInv s₀ sA t s) (he : s'.gpr .edi = s.gpr .edi)
    (hs : s'.gpr .esp = s.gpr .esp) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) (hm : s'.mem = s.mem) :
    BInv s₀ sA t s' :=
  ⟨he.trans h.edi, hs.trans h.esp, hr.trans h.rd, hw.trans h.wr, by rw [hm]; exact h.frame,
    by rw [hm]; exact h.bits⟩

theorem bit_toNat {b : Nat} (hb : b < 256) (j : Nat) :
    ((BitVec.ofNat 32 b >>> j) &&& 1).toNat = (b >>> j) &&& 1 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]
  rfl

theorem setWidth8_bit (w : BitVec 32) {b : Nat} (h : w.toNat = b) :
    w.setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

theorem and_one_le (n : Nat) : n &&& 1 ≤ 1 := Nat.le_of_lt_succ (Nat.and_lt_two_pow n (by decide : 1 < 2 ^ 1))

theorem bitOf_ok {s₀ sA s : State} (hp : Pre s₀) (hsA : sA.wr = s₀.wr) {i j : Nat} (hi : i < 32) (hj : j < 8)
    (h : BInv s₀ sA (8 * i + j) s) (heax : s.gpr .eax = BitVec.ofNat 32 (sb s₀ i))
    (hebx : s.gpr .ebx = arg s₀ 3 + BitVec.ofNat 32 (BITS + 8 * i)) :
    WP isa (.block (bitOf j)) s fun s' => BInv s₀ sA (8 * i + j + 1) s' ∧ ∀ r, r ≠ .edx → s'.gpr r = s.gpr r := by
  have hfit := hp.sc_fit
  have hbl : sb s₀ i < 256 := BitVec.isLt _
  -- The last two instructions, from `edx = eax >>> j`.
  have fin : ∀ s₁, s₁.gpr .edx = s.gpr .eax >>> j → (∀ r, r ≠ .edx → s₁.gpr r = s.gpr r) → s₁.rd = s.rd →
      s₁.wr = s.wr → s₁.mem = s.mem →
      WP isa (.block [.alu .and .edx (.imm 1), .store8 (at_ .ebx j) .dl]) s₁ fun s' =>
        BInv s₀ sA (8 * i + j + 1) s' ∧ ∀ r, r ≠ .edx → s'.gpr r = s.gpr r := by
    intro s₁ e1 g g4 g5 g6
    refine Wp.wp_andi fun s₂ u₂ => ?_
    refine wp_store8 (a := addr (arg s₀ 3) (BITS + 8 * i + j))
      (by rw [u₂.other _ (by decide), g _ (by decide), hebx]; simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat])
      ⟨_, by rw [u₂.wr, g5, h.wr, hsA]; exact hp.sc_in, scR_contains hfit (by simp only [BITS]; omega_using [hi, hj])
        (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    have ev : ((s₂.gpr (Reg8.dl).reg).setWidth 8) = BitVec.ofNat 8 ((sb s₀ i >>> j) &&& 1) := by
      refine setWidth8_bit _ ?_
      show (s₂.gpr .edx).toNat = _
      rw [u₂.gpr, e1, heax, bit_toNat hbl]
    have m₃ : s₃.mem = s.mem.writeW (addr (arg s₀ 3) (BITS + 8 * i + j)) (BitVec.ofNat 8 ((sb s₀ i >>> j) &&& 1)) := by
      rw [u₃.mem, ev, u₂.mem, g6]
    refine ⟨⟨by rw [u₃.gpr, u₂.other _ (by decide), g _ (by decide), h.edi],
      by rw [u₃.gpr, u₂.other _ (by decide), g _ (by decide), h.esp], by rw [u₃.rd, u₂.rd, g4, h.rd],
      by rw [u₃.wr, u₂.wr, g5, h.wr], ?_, fun u hu => ?_⟩, fun r hr => by rw [u₃.gpr, u₂.other _ hr, g r hr]⟩
    · rw [m₃]
      exact h.frame.writeW (List.mem_singleton_self _) _
        (sub_contains (by simp only [BITS]; omega_using [hfit]) (by simp only [BITS]; omega_using [])
          (by simp only [BITS]; omega_using [hi, hj])
          (by decide))
    · rw [m₃]
      by_cases e : u = 8 * i + j
      · subst e
        rw [show BITS + (8 * i + j) = BITS + 8 * i + j by omega_using [], byte_write_self,
          show (8 * i + j) / 8 = i by omega_using [hj], show (8 * i + j) % 8 = j by omega_using [hj]]
      · rw [byte_write_ne _ _ (by simp only [BITS]; omega_using [hfit, hu, hi, hj])
          (by simp only [BITS]; omega_using [hfit, hi, hj]) (by omega_using [e])]
        exact h.bits u (by omega_using [hu, e])
  simp only [bitOf]
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, List.nil_append, List.cons_append]
    refine Wp.wp_mov fun s₁ u₁ => fin s₁ (by rw [u₁.gpr]; exact (BitVec.ushiftRight_zero _).symm)
      (fun r hr => u₁.other _ hr) u₁.rd u₁.wr u₁.mem
  · simp only [h0, ite_false, List.cons_append, List.nil_append]
    refine Wp.wp_mov fun s₁ u₁ => Wp.wp_shr ⟨by omega_using [h0], by omega_using [hj]⟩ fun s₂ u₂ _ =>
      fin s₂ (by rw [u₂.gpr, u₁.gpr]) (fun r hr => by rw [u₂.other _ hr, u₁.other _ hr]) (by rw [u₂.rd, u₁.rd])
      (by rw [u₂.wr, u₁.wr]) (by rw [u₂.mem, u₁.mem])

theorem bitsOf_ok {s₀ sA : State} (hp : Pre s₀) (hsA : sA.wr = s₀.wr) {i : Nat} (hi : i < 32) :
    ∀ n ≤ 8, ∀ s, BInv s₀ sA (8 * i) s → s.gpr .eax = BitVec.ofNat 32 (sb s₀ i) →
    s.gpr .ebx = arg s₀ 3 + BitVec.ofNat 32 (BITS + 8 * i) →
    WP isa (.block ((List.range n).flatMap bitOf)) s fun s' =>
      BInv s₀ sA (8 * i + n) s' ∧ ∀ r, r ≠ .edx → s'.gpr r = s.gpr r
  | 0, _, _, h, _, _ => WP.block_nil ⟨h, fun _ _ => rfl⟩
  | n + 1, hn, s, h, he, hb => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitsOf_ok hp hsA hi n (by omega_using [hn]) s h he hb) fun s₁ ⟨h₁, e₁⟩ => ?_)
    exact WP.mono (bitOf_ok hp hsA hi (by omega_using [hn]) h₁ (by rw [e₁ _ (by decide), he])
      (by rw [e₁ _ (by decide), hb])) fun s₂ ⟨h₂, e₂⟩ => ⟨h₂, fun r hr => (e₂ r hr).trans (e₁ r hr)⟩

theorem scalar_contains {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    (scalarR s₀).Contains (addr (arg s₀ 1) i) 1 := by
  have := sub_contains (x := arg s₀ 1) (a := 0) (k := 32) (d := i) (n := 1)
    (by have := hp.scalar_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hi]) (by decide)
  rwa [sub, addr_zero] at this

/-- The loop over the scalar's bytes: `i` of them done. -/
def LInvS (s₀ sA : State) (i : Nat) (s : State) : Prop :=
  BInv s₀ sA (8 * i) s ∧ s.gpr .esi = arg s₀ 1 + BitVec.ofNat 32 i ∧
    s.gpr .ebx = arg s₀ 3 + BitVec.ofNat 32 (BITS + 8 * i) ∧ s.gpr .ecx = BitVec.ofNat 32 (32 - i)

theorem scalarBitsByte_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) {i : Nat} (hi : i < 32) {s : State}
    (h : LInvS s₀ sA i s) :
    WP isa (.block scalarBitsByte) s fun t => LInvS s₀ sA (i + 1) t ∧ t.zf = some (decide (32 - (i + 1) = 0)) := by
  obtain ⟨h₁, si, bi, ci⟩ := h
  have hfit := hp.sc_fit
  -- The byte of the scalar, unchanged.
  have hsame : s.mem (addr (arg s₀ 1) i) = s₀.mem (addr (arg s₀ 1) i) := by
    have f : Frame [scR 4096 (arg s₀ 3)] s₀.mem s.mem := hA.frame.trans (h₁.frame.sub fun _ hr =>
      ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr, scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by simp only [BITS]; decide)
          (by simp only [BITS]; decide)⟩)
    exact f _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.scalar_sc _ (scalar_contains hp hi)
  unfold scalarBitsByte
  refine wp_movzx8 (a := addr (arg s₀ 1) i) (by rw [si]; simp only [addr, BitVec.add_zero])
    ⟨scalarR s₀, by rw [h₁.rd, hA.rd, hp.rd]; simp, scalar_contains hp hi⟩ fun s₂ u₂ => ?_
  have h₂ : BInv s₀ sA (8 * i) s₂ := h₁.upd (u₂.other _ (by decide)) (u₂.other _ (by decide)) u₂.rd u₂.wr u₂.mem
  have e₂ : s₂.gpr .eax = BitVec.ofNat 32 (sb s₀ i) := by
    rw [u₂.gpr, hsame]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  refine WP.block_append (WP.mono (bitsOf_ok hp (by rw [hA.wr]) hi 8 (Nat.le_refl _) s₂ h₂ e₂
    (by rw [u₂.other _ (by decide), bi])) fun s₃ ⟨h₃, g₃⟩ => ?_)
  refine Wp.wp_addi fun w₁ y₁ => Wp.wp_addi fun w₂ y₂ => Wp.wp_subi fun w₃ y₃ _ z₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .edx → r ≠ .eax → s₃.gpr r = s.gpr r := fun r hr ha => by
    rw [g₃ r hr, u₂.other _ ha]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [show 8 * (i + 1) = 8 * i + 8 by omega_using []]
    exact h₃.upd (by rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.other _ (by decide)])
      (by rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.other _ (by decide)])
      (by rw [y₃.rd, y₂.rd, y₁.rd]) (by rw [y₃.wr, y₂.wr, y₁.wr]) (by rw [y₃.mem, y₂.mem, y₁.mem])
  · rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.gpr, g _ (by decide) (by decide), si,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [y₃.other _ (by decide), y₂.gpr, y₁.other _ (by decide), g _ (by decide) (by decide), bi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      show BITS + 8 * i + 8 = BITS + 8 * (i + 1) by omega_using []]
  · rw [y₃.gpr, y₂.other _ (by decide), y₁.other _ (by decide), g _ (by decide) (by decide), ci,
      Wp.ofNat_pred (by omega_using [hi])]
    congr 1
  · rw [z₃, y₂.other _ (by decide), y₁.other _ (by decide), g _ (by decide) (by decide), ci,
      Wp.ofNat_pred (by omega_using [hi]), Wp.ofNat_beq_zero (by omega_using [hi])]
    rfl

theorem scalarLoop_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) {s : State} (h : LInvS s₀ sA 0 s) :
    WP isa (.loop (.block scalarBitsByte) .ne) s (LInvS s₀ sA 32) := by
  refine WP.loop (M := isa) (Q := LInvS s₀ sA 32) (fun m t => ∃ i, m = 32 - i ∧ i < 32 ∧ LInvS s₀ sA i t) ?_ 32 s
    ⟨0, rfl, by decide, h⟩
  rintro m t ⟨i, rfl, hi, ht⟩
  refine WP.mono (scalarBitsByte_ok hp hA hi ht) fun u ⟨hu, z⟩ => ?_
  by_cases done : i + 1 = 32
  · refine .inl ⟨?_, done ▸ hu⟩
    simp only [eval, z, show 32 - (i + 1) = 0 by omega_using [done], decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, 32 - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, done], hu⟩
    simp only [eval, z, show 32 - (i + 1) ≠ 0 by omega_using [hi, done], decide_false, Option.map_some,
      Bool.not_false]

theorem kb_getD {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).getD i 0 = s₀.mem (addr (arg s₀ 1) i) := by
  simp only [Spec.X25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  rw [addr_eq (by have := hp.scalar_fit; omega_using [this, hi])]

theorem length_kb (s₀ : State) : (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).length = 32 := by
  simp [Spec.X25519.bytesAt]

/-- The scalar's bits, clamped: bit `t` of the decoded scalar at `BITS + t`. -/
theorem loadScalar_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) :
    WP isa loadScalar sA fun s' => Saved s₀ s' ∧ Frame [sub (arg s₀ 3) BITS 256] sA.mem s'.mem ∧
      ∀ t < 255, s'.mem (addr (arg s₀ 3) (BITS + t)) = BitVec.ofNat 8
        (bit (decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)) t) := by
  have hfit := hp.sc_fit
  unfold loadScalar
  refine WP.seq (Wp.wp_ldm (B := sA.gpr .esp) (o := 8) rfl
    (by rw [hA.esp, hA.rd, hA.wr]; exact hp.argIn (i := 1) (by decide))
    fun s₁ u₁ => Wp.wp_mov fun v₂ u₂ => Wp.wp_addi fun v₃ u₃ => Wp.wp_movi fun v₄ u₄ => WP.block_nil ?_)
  have e₄ : v₄.gpr .edi = sA.gpr .edi := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have h₁ : BInv s₀ sA 0 v₄ := ⟨e₄.trans hA.edi,
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)],
    by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (scalarLoop_ok hp hA ⟨h₁, ?_, ?_, by rw [u₄.gpr]; rfl⟩) fun s₂ h₂ => ?_)
  · rw [show arg s₀ 1 + BitVec.ofNat 32 0 = arg s₀ 1 from BitVec.add_zero _, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hA.esp]
    exact hp.arg_same hA.frame (i := 1) (by decide)
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hA.edi]; rfl
  replace h₂ := h₂.1
  unfold clampBits
  have inb : ∀ {s : State} {d : Nat}, s.wr = sA.wr → d < 256 →
      InRegions s.wr (addr (arg s₀ 3) (BITS + d)) 1 := fun hw hd =>
    ⟨_, by rw [hw, hA.wr]; exact hp.sc_in, scR_contains hfit (by simp only [BITS]; omega_using [hd]) (by decide)⟩
  refine Wp.wp_movi fun s₃ u₃ => ?_
  have edi₃ : s₃.gpr .edi = arg s₀ 3 := by rw [u₃.other _ (by decide)]; exact h₂.edi
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 0)) (by rw [edi₃]; rfl) (inb (by rw [u₃.wr, h₂.wr]) (by decide))
    fun s₄ u₄ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 1)) (by rw [u₄.gpr, edi₃])
    (inb (by rw [u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₅ u₅ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 2)) (by rw [u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 254)) (by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have z3 : ((s₃.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by simp only [Reg8.reg, u₃.gpr]; decide
  have z4 : ((s₄.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₄.gpr]; exact z3
  have z5 : ((s₅.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₅.gpr]; exact z4
  have o : ((s₇.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 1 := by simp only [Reg8.reg, u₇.gpr]; decide
  have m₈ : s₈.mem = ((((s₂.mem.writeW (addr (arg s₀ 3) (BITS + 0)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 1)) (0 : BitVec 8)).writeW (addr (arg s₀ 3) (BITS + 2)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 254)) (1 : BitVec 8)) := by
    rw [u₈.mem, o, u₇.mem, u₆.mem, z5, u₅.mem, z4, u₄.mem, z3, u₃.mem]
  have g : ∀ r, r ≠ .edx → s₈.gpr r = s₂.gpr r := fun r hr => by
    rw [u₈.gpr, u₇.other _ hr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ hr]
  have hb : ∀ {m : Mem} {d : Nat} (v : BitVec 8), d < 256 → Frame [sub (arg s₀ 3) BITS 256] sA.mem m →
      Frame [sub (arg s₀ 3) BITS 256] sA.mem (m.writeW (addr (arg s₀ 3) (BITS + d)) v) := fun v hd hf =>
    hf.writeW (List.mem_singleton_self _) _ (sub_contains (by simp only [BITS]; omega_using [hfit])
      (by omega_using []) (by omega_using [hd]) (by decide))
  have f₈ : Frame [sub (arg s₀ 3) BITS 256] sA.mem s₈.mem := by
    rw [m₈]; exact hb _ (by decide) (hb _ (by decide) (hb _ (by decide) (hb _ (by decide) h₂.frame)))
  refine ⟨hA.of_frame hp f₈ (by decide) (by decide) (by decide) (by rw [g _ (by decide), h₂.edi, hA.edi])
    (by rw [g _ (by decide), h₂.esp]) (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]), f₈, fun t ht => ?_⟩
  rw [scalar_bit (length_kb s₀) ht, m₈]
  have ne : ∀ (m : Mem) (v : BitVec 8) (e : Nat), e < 256 → t ≠ e →
      (m.writeW (addr (arg s₀ 3) (BITS + e)) v) (addr (arg s₀ 3) (BITS + t)) = m (addr (arg s₀ 3) (BITS + t)) :=
    fun m v e he h => byte_write_ne m v (by simp only [BITS]; omega_using [hfit, ht])
      (by simp only [BITS]; omega_using [hfit, he]) (by omega_using [h])
  by_cases h3 : t < 3
  · rw [ite_eq_left h3, ne _ _ 254 (by decide) (by omega_using [h3])]
    rcases (by omega_using [h3] : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
    · rw [ne _ _ 2 (by decide) (by decide), ne _ _ 1 (by decide) (by decide), byte_write_self]; rfl
    · rw [ne _ _ 2 (by decide) (by decide), byte_write_self]; rfl
    · rw [byte_write_self]; rfl
  · rw [ite_eq_right h3]
    by_cases h254 : t = 254
    · subst h254; rw [ite_eq_left rfl, byte_write_self]; rfl
    · rw [ite_eq_right h254, ne _ _ 254 (by decide) h254, ne _ _ 2 (by decide) (by omega_using [h3]),
        ne _ _ 1 (by decide) (by omega_using [h3]), ne _ _ 0 (by decide) (by omega_using [h3]),
        h₂.bits t (by omega_using [ht]), kb_getD hp (by omega_using [ht])]

/-! ## The ladder's initial state -/

theorem setSmall_step {x : BitVec 32} {s₀ s : State} (hc : Ctx 4096 x s) {o n : Nat} (ho : Below o) (hn : n < 8)
    (c : BitVec 32) (hk : Keep s₀ s) (hf : Frame [sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, wd s.mem x (o + 4 * j) = if j = 0 then c else 0) :
    WP isa (.block [.mov .eax (.imm (if n = 0 then c else 0)), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, wd s'.mem x (o + 4 * j) = if j = 0 then c else 0 := by
  simp only [Below, T] at ho
  have hfit := hc.fit
  refine Wp.wp_movi fun s₁ u₁ => ?_
  have c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨hk.trans ((updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact frame_write1 (frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.mem]
    by_cases e : j = n
    · subst e; rw [wd_write_self, u₁.gpr]
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem setSmalls_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx 4096 x s₀) {o : Nat} (ho : Below o) (c : BitVec 32) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.imm (if k = 0 then c else 0)), .store (sc (o + 4 * k)) .eax])) s₀ fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * n)] s₀.mem s'.mem ∧
        ∀ j < n, wd s'.mem x (o + 4 * j) = if j = 0 then c else 0
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (setSmalls_ok hc₀ ho c n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      setSmall_step (k₁.ctx hc₀) ho (by omega_using [hn]) c k₁ f₁ w₁)

/-- `[o] = c`. -/
theorem setSmall_ok {x : BitVec 32} {s : State} (hc : Ctx 4096 x s) {o : Nat} (ho : Below o) (c : BitVec 32) :
    WP isa (.block (setSmall o c)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o = c.toNat :=
  WP.mono (setSmalls_ok hc ho c 8 (Nat.le_refl _)) fun _ ⟨k, f, w⟩ => ⟨k, f, by
    rw [fe]
    rw [num_congr (g := fun j => if j = 0 then c.toNat else 0) fun j hj => by
      show (wd _ x (o + 4 * j)).toNat = _; rw [w j hj]; split <;> rfl]
    simp only [num, Nat.reduceEqDiff, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add]⟩

theorem F_setSmall {x : BitVec 32} {s' : State} {o : Nat} (c : BitVec 32) (h : fe s'.mem x o = c.toNat) :
    F s'.mem x o = toFe c.toNat := by simp only [F, h]

/-- The slots, other than `o`, after a frame of `o`'s. -/
theorem F_frame1 {m m' : Mem} {x : BitVec 32} {o q : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x o 32] m m') (ho : isSlot 288 o = true) (hq : isSlot 288 q = true) (hne : q ≠ o) :
    F m' x q = F m x q := by
  have hob := slot_below ho; have hqb := slot_below hq; simp only [Below, T] at hob hqb
  simp only [F]
  exact congrArg toFe (fe_frame1 hf hx (by omega_using [hob]) (by omega_using [hqb]) (slot_ne ho hq hne))

theorem frame_slot {m m' : Mem} {x : BitVec 32} {o : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x o 32] m m') (ho : isSlot 288 o = true) : Frame [sub x 288 640] m m' := by
  have hob := slot_below ho; have ho' := slot_ge ho; simp only [Below, T] at hob
  exact frameWiden hf hx ho' (by omega_using [hob]) (by omega_using [hob])

/-- The u-coordinate as `X1` holds it: decoded (RFC 7748 §5). -/
theorem fe_X1 {s₀ s : State} (hp : Pre s₀) (hw : ∀ j < 8, wd s.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j) :
    fe s.mem (arg s₀ 3) X1 = decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
  have hpf := hp.point_fit
  have e1 : fe s.mem (arg s₀ 3) X1 = num (fun k => (pv s₀ k).toNat) 8 :=
    num_congr fun j hj => by show (wd _ _ _).toNat = _; rw [hw j hj]
  have e2 : num (fun k => (pv s₀ k).toNat) 8 = num (fun k => (pw s₀ k).toNat) 8 % 2 ^ 255 := by
    rw [(fold_top (f := fun k => (pw s₀ k).toNat) fun _ _ => BitVec.isLt _).1, num_top]
    have n7 : num (fun k => (pv s₀ k).toNat) 7 = num (fun k => (pw s₀ k).toNat) 7 :=
      num_congr fun j hj => by
        show (pv s₀ j).toNat = (pw s₀ j).toNat
        rw [pv, ite_eq_right (show j ≠ 7 by omega_using [hj])]
    rw [n7]
    simp only [pv, ite_true, low31_toNat]
  have e3 : num (fun k => (pw s₀ k).toNat) 8 = leNum (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
    rw [leNum_bytesAt_words32]
    have r : ∀ k < 8, (pw s₀ k).toNat =
        (s₀.mem.readW ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32).toNat := fun k hk => by
      simp only [pw, wd]; rw [addr_eq (by omega_using [hpf, hk])]
    simp only [num, r 0 (by decide), r 1 (by decide), r 2 (by decide), r 3 (by decide), r 4 (by decide),
      r 5 (by decide), r 6 (by decide), r 7 (by decide), Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      Nat.reduceMul, Nat.reducePow, Nat.one_mul, Nat.zero_add]
  rw [e1, e2, e3, decodeUCoordinate_eq (length_bytesAt _ _ _)]

/-- The scalar, decoded. -/
abbrev kOf (s₀ : State) : Nat := decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)

/-- The u-coordinate, decoded. -/
abbrev uOf (s₀ : State) : Fe := toFe (decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32))

theorem initLadder_eq : initLadder = copy X3 X1 ++ (setSmall X2 1 ++
    (setSmall Z2 0 ++ (setSmall Z3 1 ++ ([.mov .eax (.imm 0), .store (sc SWAP) .eax] : List Instr)))) := by
  simp only [initLadder, List.append_assoc]

/-- The arguments read: the ladder's initial state, in `LInv 255` but for the counter. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa setup s₀ fun s => Base (arg s₀ 3) (kOf s₀) s₀ s ∧ F s.mem (arg s₀ 3) X1 = uOf s₀ ∧
      F s.mem (arg s₀ 3) X2 = 1 ∧ F s.mem (arg s₀ 3) Z2 = 0 ∧ F s.mem (arg s₀ 3) X3 = uOf s₀ ∧
      F s.mem (arg s₀ 3) Z3 = 1 ∧ wd s.mem (arg s₀ 3) SWAP = 0 := by
  have hfit := hp.sc_fit
  unfold setup
  refine WP.seq (WP.block_append (WP.mono (save_ok hp) fun s₁ h₁ => ?_))
  refine WP.mono (loadPoint_ok hp h₁) fun s₂ ⟨h₂, w₂⟩ => ?_
  refine WP.seq (WP.mono (loadScalar_ok hp h₂) fun s₃ ⟨h₃, f₃, b₃⟩ => ?_)
  rw [initLadder_eq]
  have B₃ : Base (arg s₀ 3) (kOf s₀) s₀ s₃ :=
    ⟨⟨h₃.edi, hfit, by rw [h₃.wr]; exact hp.sc_in, by decide, fun _ hW => absurd hW (by decide)⟩, h₃.esp, h₃.rd, h₃.wr, h₃.frame, h₃.saved, b₃⟩
  have x1₃ : F s₃.mem (arg s₀ 3) X1 = uOf s₀ := by
    simp only [F, uOf]
    rw [← fe_X1 hp w₂]
    exact congrArg toFe (fe_frame1 f₃ hfit (by decide) (by decide) (.inr (by decide)))
  have sl : ∀ q, isSlot 288 q = true → Below q := fun q hq => slot_below hq
  refine WP.block_append (WP.mono (copy_ok B₃.ctx (o := X3) (a := X1) (by decide) (by decide) (by decide))
    fun s₄ ⟨k₄, f₄, e₄⟩ => ?_)
  have B₄ := B₃.ops k₄ (frame_slot hfit f₄ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₄.ctx (o := X2) (by decide) 1) fun s₅ ⟨k₅, f₅, e₅⟩ => ?_)
  have B₅ := B₄.ops k₅ (frame_slot hfit f₅ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₅.ctx (o := Z2) (by decide) 0) fun s₆ ⟨k₆, f₆, e₆⟩ => ?_)
  have B₆ := B₅.ops k₆ (frame_slot hfit f₆ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₆.ctx (o := Z3) (by decide) 1) fun s₇ ⟨k₇, f₇, e₇⟩ => ?_)
  have B₇ := B₆.ops k₇ (frame_slot hfit f₇ (by decide))
  refine Wp.wp_movi fun s₈ u₈ => ?_
  have c₈ := (updKeep u₈).ctx B₇.ctx
  refine Wp.wp_stm c₈.edi (c₈.inW (by decide) (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₇.mem.writeW (addr (arg s₀ 3) SWAP) (0 : BitVec 32) := by rw [u₉.mem, u₈.gpr, u₈.mem]
  have f₉ : Frame [sub (arg s₀ 3) SWAP 4] s₇.mem s₉.mem := by
    rw [m₉]; exact frame_write1 (Frame.refl _ _) hfit (by decide) (Nat.le_refl _) (Nat.le_refl _) _
  have F₉ : ∀ q, isSlot 288 q = true → F s₉.mem (arg s₀ 3) q = F s₇.mem (arg s₀ 3) q := fun q hq => by
    have hq' := slot_ge hq; have hqb := slot_below hq; simp only [Below, T] at hqb
    simp only [F]
    exact congrArg toFe (fe_frame1 f₉ hfit (by decide) (by omega_using [hqb]) (.inr (by simp only [SWAP]; omega_using [hq'])))
  refine ⟨B₇.of_frame (by rw [u₉.gpr, u₈.other _ (by decide)]) (by rw [u₉.gpr, u₈.other _ (by decide)])
    (by rw [u₉.rd, u₈.rd]) (by rw [u₉.wr, u₈.wr]) f₉ (by decide) (by decide) (.inl (by decide)) (by decide),
    ?_, ?_, ?_, ?_, ?_, by rw [m₉, wd_write_self]⟩
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_frame1 hfit f₅ (by decide) (by decide) (by decide),
      F_frame1 hfit f₄ (by decide) (by decide) (by decide), x1₃]
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_setSmall _ e₅]; rfl
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide), F_setSmall _ e₆]; rfl
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_frame1 hfit f₅ (by decide) (by decide) (by decide)]
    simp only [F] at x1₃ ⊢
    rw [e₄]; exact x1₃
  · rw [F₉ _ (by decide), F_setSmall _ e₇]; rfl

end VG.Proof.X25519.X86
