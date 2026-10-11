import VerifiedGarbage.Proof.Idea.X86.Key
import VerifiedGarbage.Proof.Idea.X86.Block
import VerifiedGarbage.Proof.Idea.Inverse
import VerifiedGarbage.Proof.Idea.Scratch32

/-!
# IDEA decryption subkeys on x86 (32-bit)

With the scratch buffer as an argument (four words), `invertKey` saves
`ebx`, `esi`, `edi`, `ebp` in it and restores them at the end. Each
decryption subkey is a copy, the negation or the inverse of an encryption
subkey (at `esi`; `invertKey_getD`, `Impl.Idea.invOp`), computed into `ecx`
(`invWord_ok`; the inverse by a loop of fifteen steps of `t := (t ⊙ t) ⊙ a`,
`invLoop_ok`) and stored a byte at a time at `edi` (`invStore_run`).
-/

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86 VG.Impl.Idea

/-! ## Reading the subkeys -/

/-- The encryption subkeys `z` at `esi`, readable, not wrapping around. -/
structure SchedOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  read : ⟨(s.gpr .esi).setWidth 64, 104⟩ ∈ s.rd ++ s.wr
  fit : (s.gpr .esi).toNat + 104 ≤ 2 ^ 32
  sched : Spec.Idea.scheduleAt s.mem ((s.gpr .esi).setWidth 64) = z

theorem SchedOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : SchedOk z s)
    (hk : Keep rs s s') (hesi : .esi ∉ rs) : SchedOk z s' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hk.rd, hk.wr, hk.reg .esi hesi]; exact h.read
  · rw [hk.reg .esi hesi]; exact h.fit
  · rw [hk.mem, hk.reg .esi hesi]; exact h.sched

theorem SchedOk.word {z : Spec.Idea.Schedule} {s : State} (h : SchedOk z s) {d : Nat} (hd : d + 4 ≤ 104) :
    readSrc s (.mem (at_ .esi d)) = some (s.mem.readW ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32) := by
  have ha := addr_eq (x := s.gpr .esi) (k := d) (by have := h.fit; omega)
  rw [load_src (by rw [ha]; exact ⟨_, h.read, Offset.contains_base _ hd (by omega)⟩), ha]

/-- `loadKey r k`: subkey `k` in the low 16 bits of `r`. -/
theorem loadKey_run (z : Spec.Idea.Schedule) (r : Reg) (k : Nat) (hk52 : k < 52) (s : State)
    (h : SchedOk z s) :
    ∃ s', runBlock isa (loadKey r k) s = some s' ∧ (s'.gpr r).setWidth 16 = z.getD k 0 ∧
      Keep [r] s s' := by
  unfold loadKey
  split
  · rename_i hk; subst hk
    obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run r _ _ s (h.word (d := 100) (by decide))
    obtain ⟨s₂, h₂, v₂, e₂⟩ := shift_run .shr r 16 (by decide) s₁
    refine ⟨s₂, run_append h₁ h₂, ?_, e₁.trans e₂⟩
    simp only at v₂
    rw [v₂, v₁, subkey_hi32, h.sched]
  · obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run r _ _ s (h.word (d := 2 * k) (by omega))
    exact ⟨s₁, h₁, by rw [v₁, subkey_lo32 _ _ hk52, h.sched], e₁⟩

/-! ## The inverse -/

theorem sub1_run (r : Reg) (s : State) :
    ∃ s', runBlock isa [.alu .sub r (.imm 1)] s = some s' ∧ s'.gpr r = s.gpr r - 1 ∧
      s'.zf = some (s.gpr r - 1 == 0) ∧ Keep [r] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and]
  exact ⟨rfl, by keep_tac⟩

theorem invStep_run (t : State) :
    ∃ t', runBlock isa invStep t = some t' ∧
      t'.gpr .ecx = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .ecx).setWidth 16) ((t.gpr .ecx).setWidth 16))
        ((t.gpr .ebx).setWidth 16)).setWidth 32 ∧
      t'.gpr .ebp = t.gpr .ebp - 1 ∧ t'.zf = some (t.gpr .ebp - 1 == 0) ∧
      Keep [.eax, .ecx, .edx, .ebp] t t' := by
  obtain ⟨t₁, h₁, v₁, e₁⟩ := mov_run .eax (.reg .ecx) _ t rfl
  obtain ⟨t₂, h₂, v₂, e₂⟩ := mul_run (.reg .ecx) (t₁.gpr .ecx) t₁
    (fun u _ _ _ hg => by simp only [readSrc, hg .ecx (by decide)])
  obtain ⟨t₃, h₃, v₃, e₃⟩ := mov_run .eax (.reg .edx) _ t₂ rfl
  obtain ⟨t₄, h₄, v₄, e₄⟩ := mul_run (.reg .ebx) (t₃.gpr .ebx) t₃
    (fun u _ _ _ hg => by simp only [readSrc, hg .ebx (by decide)])
  obtain ⟨t₅, h₅, v₅, e₅⟩ := mov_run .ecx (.reg .edx) _ t₄ rfl
  obtain ⟨t₆, h₆, v₆, z₆, e₆⟩ := sub1_run .ebp t₅
  have e₀₄ : Keep [.eax, .edx] t t₄ := (((e₁.weaken (by decide)).trans e₂).trans (e₃.weaken (by decide))).trans e₄
  have ebp₅ : t₅.gpr .ebp = t.gpr .ebp := (e₅.reg .ebp (by decide)).trans (e₀₄.reg .ebp (by decide))
  refine ⟨t₆, ?_, ?_, by rw [v₆, ebp₅], by rw [z₆, ebp₅], ?_⟩
  · unfold invStep
    exact run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) (run_append (a := [_]) h₅ h₆)
  · rw [e₆.reg .ecx (by decide), v₅, v₄, v₃, v₂, v₁, e₃.reg .ebx (by decide), e₂.reg .ebx (by decide),
      e₁.reg .ebx (by decide), e₁.reg .ecx (by decide), setWidth_setWidth16_32]
  · exact ((e₀₄.weaken (by decide)).trans (e₅.weaken (by decide))).trans (e₆.weaken (by decide))

/-- `c` steps remain: `ecx` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  ebp : t.gpr .ebp = BitVec.ofNat 32 c
  ebx : (t.gpr .ebx).setWidth 16 = a
  ecx : (t.gpr .ecx).setWidth 16 = chain a (15 - c)
  keep : Keep [.eax, .ecx, .edx, .ebp] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) .ne) t (fun t' =>
      t'.gpr .ecx = (Spec.Idea.inv a).setWidth 32 ∧ Keep [.eax, .ecx, .edx, .ebp] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  obtain ⟨t', h', ecx', ebp', z', e'⟩ := invStep_run t
  refine WP.of_runBlock ⟨t', h', ?_⟩
  have hv : t'.gpr .ecx = (chain a (15 - c + 1)).setWidth 32 := by
    rw [ecx', hi.ecx, hi.ebx]; rfl
  have hc : t'.gpr .ebp = BitVec.ofNat 32 (c - 1) := by
    rw [ebp', hi.ebp]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  have hev : isa.eval .ne t' = some (decide (c - 1 ≠ 0)) := by
    show t'.zf.map (!·) = _
    rw [z', ← ebp', hc, Option.map_some]
    congr 1
    have := hi.le
    by_cases h0 : c - 1 = 0
    · simp only [h0]; rfl
    · have hne : BitVec.ofNat 32 (c - 1) ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this)
      rw [show (BitVec.ofNat 32 (c - 1) == 0) = false from by simpa using hne]
      simp [h0]
  have keep' : Keep [.eax, .ecx, .edx, .ebp] t₀ t' := hi.keep.trans e'
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨hev, ?_, keep'⟩
    rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega,
      c - 1, by omega, by omega, by omega, hc, ?_, ?_, keep'⟩
    · rw [e'.reg .ebx (by decide)]; exact hi.ebx
    · rw [hv, setWidth_setWidth16_32, show 15 - c + 1 = 15 - (c - 1) by omega]

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : SchedOk z t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .ecx = ((Spec.Idea.invertKey z).getD n 0).setWidth 32 ∧ Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  have hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .ecx k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := alu_run .and (by simp) .ecx (.imm 0xffff) 0xffff t₁ rfl
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, (e₁.weaken (by decide)).trans (e₂.weaken (by decide))⟩
    simp only [aluF] at v₂
    rw [v₂, mask32_setWidth, v₁]; rfl
  | neg =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .edx k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := mov_run .ecx (.imm 0) 0 t₁ rfl
    obtain ⟨t₃, h₃, v₃, e₃⟩ := alu_run .sub (by simp) .ecx (.reg .edx) _ t₂ rfl
    obtain ⟨t₄, h₄, v₄, e₄⟩ := alu_run .and (by simp) .ecx (.imm 0xffff) 0xffff t₃ rfl
    refine WP.of_runBlock ⟨t₄, run_append h₁ (run_append h₂ (run_append h₃ h₄)), ?_, ?_⟩
    · simp only [aluF] at v₃ v₄
      rw [v₄, v₃, v₂, e₂.reg .edx (by decide), neg_mask32, v₁]; rfl
    · exact (((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans
        (e₄.weaken (by decide))
  | inv =>
    apply WP.seq
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .ebx k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := mov_run .ecx (.reg .ebx) _ t₁ rfl
    obtain ⟨t₃, h₃, v₃, e₃⟩ := mov_run .ebp (.imm 15) 15 t₂ rfl
    refine WP.of_runBlock ⟨t₃, run_append h₁ (run_append h₂ h₃), ?_⟩
    have ebx₃ : t₃.gpr .ebx = t₁.gpr .ebx := by rw [e₃.reg .ebx (by decide), e₂.reg .ebx (by decide)]
    refine WP.mono (invLoop_ok (z.getD k 0) t₃ 15 t₃ ⟨by decide, by decide, v₃, by rw [ebx₃, v₁],
      by rw [e₃.reg .ecx (by decide), v₂, v₁]; rfl, Keep.refl _ _⟩) fun t₄ h₄ => ?_
    obtain ⟨ecx₄, e₄⟩ := h₄
    refine ⟨ecx₄, ?_⟩
    exact (((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))).trans
      (e₄.weaken (by decide))

/-! ## Storing a subkey -/

theorem writeW8_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.reduceDiv,
    Nat.zero_lt_one, ite_true, Nat.mul_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem writeW8_ne (m : Mem) (O : Addr) (v : BitVec 8) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : i ≠ j) : (m.writeW (O + BitVec.ofNat 64 j) v) (O + BitVec.ofNat 64 i) = m (O + BitVec.ofNat 64 i) := by
  refine Mem.write_apply ?_
  rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem split16 (x : BitVec 16) : ((x >>> 8).setWidth 8 ++ x.setWidth 8 : BitVec 16) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 8
  · simp [h]
  · simp only [h, ite_false, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show i - 8 < 8 by omega, decide_true, Bool.true_and]
    congr 1; omega

theorem store8_run (b : Reg) (d : Nat) (r : Reg8) (s : State) (h : InRegions s.wr (addr (s.gpr b) d) 1) :
    ∃ s', runBlock isa [.store8 (at_ b d) r] s = some s' ∧
      s'.mem = s.mem.writeW (addr (s.gpr b) d) ((s.gpr r.reg).setWidth 8) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions s.wr (s.ea (at_ b d)) 1 := h
  simp only [runBlock_cons, isa, exec, State.store8, hin, ite_true, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- The output (104 bytes at `edi`, address `O`) writable, not wrapping around. -/
structure OutOk (O : Addr) (s : State) : Prop where
  wr : ⟨O, 104⟩ ∈ s.wr
  addr : (s.gpr .edi).setWidth 64 = O
  fit : (s.gpr .edi).toNat + 104 ≤ 2 ^ 32

theorem invStore_run {O : Addr} (n : Nat) (hn : n < 52) (v : Spec.Idea.Word) (s : State) (ho : OutOk O s)
    (hv : s.gpr .ecx = v.setWidth 32) :
    ∃ s', runBlock isa (invStore n) s = some s' ∧
      s'.mem = (s.mem.writeW (O + BitVec.ofNat 64 (2 * n)) (v.setWidth 8)).writeW
        (O + BitVec.ofNat 64 (2 * n + 1)) ((v >>> 8).setWidth 8) ∧ Keep [.ecx] { s with mem := s'.mem } s' := by
  have ha : ∀ d, d < 104 → addr (s.gpr .edi) d = O + BitVec.ofNat 64 d := fun d hd => by
    rw [addr_eq (by have := ho.fit; omega), ho.addr]
  obtain ⟨s₁, h₁, m₁, g₁, rd₁, wr₁⟩ := store8_run .edi (2 * n) .cl s
    (by rw [ha _ (by omega)]; exact ⟨_, ho.wr, Offset.contains_base _ (by omega) (by omega)⟩)
  obtain ⟨s₂, h₂, v₂, e₂⟩ := shift_run .shr .ecx 8 (by decide) s₁
  have edi₂ : s₂.gpr .edi = s.gpr .edi := by rw [e₂.reg .edi (by decide), g₁]
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store8_run .edi (2 * n + 1) .cl s₂
    (by rw [edi₂, ha _ (by omega), e₂.wr, wr₁]; exact ⟨_, ho.wr, Offset.contains_base _ (by omega) (by omega)⟩)
  refine ⟨s₃, run_append h₁ (run_append h₂ h₃), ?_, ⟨fun q hq => ?_, rfl, ?_, ?_⟩⟩
  · simp only at v₂
    rw [m₃, e₂.mem, m₁, edi₂, ha _ (by omega), ha _ (by omega)]
    simp only [Reg8.reg]
    rw [v₂, g₁, hv, lo8_32, hi8_32]
  · simp only [List.mem_singleton] at hq
    rw [g₃, e₂.reg q (by simpa using hq), g₁]
  · show s₃.rd = s.rd; rw [rd₃, e₂.rd, rd₁]
  · show s₃.wr = s.wr; rw [wr₃, e₂.wr, wr₁]

/-! ## All the subkeys -/

/-- After `n` decryption subkeys, from `s₀` (subkeys at `esi`, output at `O`). -/
structure SInv (z : Spec.Idea.Schedule) (O : Addr) (s₀ : State) (n : Nat) (t : State) : Prop where
  keep : Keep invWrites s₀ { t with mem := s₀.mem }
  frame : Frame [⟨O, 2 * n⟩] s₀.mem t.mem
  words : ∀ i < n, t.mem (O + BitVec.ofNat 64 (2 * i + 1)) ++ t.mem (O + BitVec.ofNat 64 (2 * i)) = dk z i

theorem SInv.ok {z : Spec.Idea.Schedule} {O : Addr} {s₀ t : State} {n : Nat} (hi : SInv z O s₀ n t)
    (hz : SchedOk z s₀) (ho : OutOk O s₀) (hsep : Region.Disjoint ⟨(s₀.gpr .esi).setWidth 64, 104⟩ ⟨O, 104⟩)
    (hn : n ≤ 52) : SchedOk z t ∧ OutOk O t := by
  have esi : t.gpr .esi = s₀.gpr .esi := hi.keep.reg .esi (by decide)
  have edi : t.gpr .edi = s₀.gpr .edi := hi.keep.reg .edi (by decide)
  refine ⟨⟨by rw [esi, hi.keep.rd, hi.keep.wr]; exact hz.read, by rw [esi]; exact hz.fit, ?_⟩,
    ⟨by rw [hi.keep.wr]; exact ho.wr, by rw [edi]; exact ho.addr, by rw [edi]; exact ho.fit⟩⟩
  rw [esi, ← hz.sched]
  exact scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hsep.sub_right (Region.sub_prefix (by omega))) (by decide))

theorem subkey_ok (z : Spec.Idea.Schedule) {O : Addr} (s₀ : State) (hz : SchedOk z s₀) (ho : OutOk O s₀)
    (hsep : Region.Disjoint ⟨(s₀.gpr .esi).setWidth 64, 104⟩ ⟨O, 104⟩) (n : Nat) (hn : n < 52) (t : State)
    (hi : SInv z O s₀ n t) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t', SInv z O s₀ (n + 1) t' → WP isa rest t' Q) :
    WP isa (.seq (invWord n) (.seq (.block (invStore n)) rest)) t Q := by
  obtain ⟨hz', ho'⟩ := hi.ok hz ho hsep (by omega)
  apply WP.seq
  refine WP.mono (invWord_ok z hn t hz') fun t₁ h₁ => ?_
  obtain ⟨v₁, e₁⟩ := h₁
  apply WP.seq
  have ho₁ : OutOk O t₁ := ⟨by rw [e₁.wr]; exact ho'.wr, by rw [e₁.reg .edi (by decide)]; exact ho'.addr,
    by rw [e₁.reg .edi (by decide)]; exact ho'.fit⟩
  obtain ⟨t₂, h₂, m₂, e₂⟩ := invStore_run n hn _ t₁ ho₁ v₁
  refine WP.of_runBlock ⟨t₂, h₂, hrest t₂ ⟨?_, ?_, fun i hin => ?_⟩⟩
  · refine ⟨fun q hq => ?_, rfl, ?_, ?_⟩
    · show t₂.gpr q = s₀.gpr q
      rw [e₂.reg q (fun h => hq (by simp at h; simp [h])), e₁.reg q hq]
      exact hi.keep.reg q hq
    · show t₂.rd = s₀.rd; rw [e₂.rd, e₁.rd]; exact hi.keep.rd
    · show t₂.wr = s₀.wr; rw [e₂.wr, e₁.wr]; exact hi.keep.wr
  · rw [m₂, e₁.mem]
    refine ((hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)
  · rw [m₂, e₁.mem]
    by_cases he : i = n
    · subst he
      rw [writeW8_self, writeW8_ne _ _ _ (by omega) (by omega) (by omega), writeW8_self, split16]
    · rw [writeW8_ne _ _ _ (by omega) (by omega) (by omega), writeW8_ne _ _ _ (by omega) (by omega) (by omega),
        writeW8_ne _ _ _ (by omega) (by omega) (by omega), writeW8_ne _ _ _ (by omega) (by omega) (by omega)]
      exact hi.words i (by omega)

/-- Subkeys `q … q + n - 1`. -/
def subkeys (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun n rest => .seq (invWord n) (.seq (.block (invStore n)) rest)) (.block [])

theorem subkeys_ok (z : Spec.Idea.Schedule) {O : Addr} (s₀ : State) (hz : SchedOk z s₀) (ho : OutOk O s₀)
    (hsep : Region.Disjoint ⟨(s₀.gpr .esi).setWidth 64, 104⟩ ⟨O, 104⟩) :
    ∀ n q, q + n = 52 → ∀ t, SInv z O s₀ q t → WP isa (subkeys q n) t (SInv z O s₀ 52)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [subkeys, List.range'_succ, List.foldr_cons]
    exact subkey_ok z s₀ hz ho hsep q (by omega) t hi fun t₁ h₁ =>
      subkeys_ok z s₀ hz ho hsep n (q + 1) (by omega) t₁ h₁

theorem invertKey_eq : invertKey =
    .seq (.block (([.mov .eax (.mem (argOp 2))] : List Instr) ++ saveAt .eax 0 ++
      ([.mov .esi (.mem (argOp 0)), .mov .edi (.mem (argOp 1))] : List Instr)))
    (.seq (subkeys 0 52) (.block (([.mov .eax (.mem (argOp 2))] : List Instr) ++ restoreAt .eax 0))) :=
  rfl

/-! ## The function -/

/-- `vg_idea_invert_key` on x86, with the scratch buffer (16 bytes) as its
third argument. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 104⟩
    let out : Region := ⟨(arg s 1).setWidth 64, 104⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [out, scratch] ∧ sched.Disjoint out ∧ sched.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + 104 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 104 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := Spec.Idea.scheduleAt s'.mem ((arg s 1).setWidth 64) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

/-- The arguments read the same after writes outside them. -/
theorem arg_frame {s t : State} {rs : List Region} {n : Nat} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨argAddr s 0, n⟩ r) (hesp : t.gpr .esp = s.gpr .esp)
    (hfit : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {i : Nat} (hi : 4 * i + 4 ≤ n) : arg t i = arg s i := by
  have ha : argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [argAddr]
    rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s.gpr .esp) (4 + 4 * i) from rfl,
      show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s.gpr .esp) 4 from rfl,
      addr_eq (by omega), addr_eq (by omega), Offset.add_ofNat_add_ofNat]
  simp only [arg, show argAddr t i = argAddr s i by simp only [argAddr, hesp]]
  rw [ha]
  exact hf.readW (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem invert_wp (s : State) (hs : invertContract.pre s) :
    WP isa invertKey s (fun s' => abiPreserved s s' ∧ invertContract.post s s') := by
  obtain ⟨hrd, hwr, dSO, dSB, dOB, dAO, dAB, dRO, dRB, fitS, fitO, fitB, fitSp⟩ := hs
  have hargs : ⟨argAddr s 0, 12⟩ ∈ s.rd := by rw [hrd]; simp
  rw [invertKey_eq]
  -- The prologue.
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (arg_src (i := 2) (by decide) hargs (by omega))
  have hB : ∀ d, d + 4 ≤ 16 → addr (s₁.gpr .eax) d = (arg s 2).setWidth 64 + BitVec.ofNat 64 d :=
    fun d hd => by rw [v₁, addr_eq (by omega)]
  have inB : ∀ d, d + 4 ≤ 16 → ∀ t : State, t.wr = s.wr → InRegions t.wr (addr (s₁.gpr .eax) d) 4 :=
    fun d hd t ht => by
      rw [hB d hd, ht, hwr]
      exact ⟨_, by simp, Offset.contains_base _ hd (by omega)⟩
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂⟩ := store_run .eax .ebx 0 s₁ (inB 0 (by decide) _ e₁.wr)
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store_run .eax .esi 4 s₂
    (by rw [g₂]; exact inB 4 (by decide) _ (by rw [wr₂, e₁.wr]))
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄⟩ := store_run .eax .edi 8 s₃
    (by rw [g₃, g₂]; exact inB 8 (by decide) _ (by rw [wr₃, wr₂, e₁.wr]))
  obtain ⟨s₅, h₅, m₅, g₅, rd₅, wr₅⟩ := store_run .eax .ebp 12 s₄
    (by rw [g₄, g₃, g₂]; exact inB 12 (by decide) _ (by rw [wr₄, wr₃, wr₂, e₁.wr]))
  have g₁₅ : s₅.gpr = s₁.gpr := by rw [g₅, g₄, g₃, g₂]
  have rd₁₅ : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃, rd₂, e₁.rd]
  have wr₁₅ : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃, wr₂, e₁.wr]
  have esp₅ : s₅.gpr .esp = s.gpr .esp := by rw [g₁₅, e₁.reg .esp (by decide)]
  -- The saved registers, in the scratch buffer.
  have fB : Frame [⟨(arg s 2).setWidth 64, 16⟩] s.mem s₅.mem := by
    rw [m₅, m₄, m₃, m₂, e₁.mem, g₄, g₃, g₂, hB 0 (by decide), hB 4 (by decide), hB 8 (by decide),
      hB 12 (by decide)]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have saved : ∀ r d, (r, d) ∈ [(Reg.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)] →
      s₅.mem.readW ((arg s 2).setWidth 64 + BitVec.ofNat 64 d) 32 = s.gpr r := by
    intro r d hrd'
    have g1 : ∀ q, q ≠ .eax → s₁.gpr q = s.gpr q := fun q hq => e₁.reg q (by simpa using hq)
    rw [m₅, m₄, m₃, m₂, e₁.mem, g₄, g₃, g₂, hB 0 (by decide), hB 4 (by decide), hB 8 (by decide),
      hB 12 (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd'
    have sep : ∀ a b, a + 4 ≤ b ∨ b + 4 ≤ a → b + 4 ≤ 16 → a + 4 ≤ 16 →
        Mem.Sep ((arg s 2).setWidth 64 + BitVec.ofNat 64 a) (32 / 8) ((arg s 2).setWidth 64 + BitVec.ofNat 64 b) (32 / 8) :=
      fun a b h hb ha => Offset.sep _ h (by omega) (by omega)
    rcases hrd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Mem.readW_writeW_sep (sep 0 12 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 0 8 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 0 4 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32, g1 _ (by decide)]
    · rw [Mem.readW_writeW_sep (sep 4 12 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 4 8 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32, g1 _ (by decide)]
    · rw [Mem.readW_writeW_sep (sep 8 12 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32, g1 _ (by decide)]
    · rw [Mem.readW_writeW_self32, g1 _ (by decide)]
  -- The pointers.
  have hargs₅ : ⟨argAddr s₅ 0, 12⟩ ∈ s₅.rd := by
    rw [rd₁₅]; simp only [argAddr, esp₅]; exact hargs
  have argE : ∀ i, i < 3 → arg s₅ i = arg s i := fun i hi =>
    arg_frame fB (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAB) esp₅ (by omega)
      (by omega)
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .esi _ _ s₅ (arg_src (i := 0) (by decide) hargs₅ (by rw [esp₅]; omega))
  have hargs₆ : ⟨argAddr s₆ 0, 12⟩ ∈ s₆.rd := by
    rw [e₆.rd]; simp only [argAddr, e₆.reg .esp (by decide)]; exact hargs₅
  obtain ⟨s₇, h₇, v₇, e₇⟩ := mov_run .edi _ _ s₆ (arg_src (i := 1) (by decide) hargs₆
    (by rw [e₆.reg .esp (by decide), esp₅]; omega))
  have a₆ : arg s₆ 1 = arg s 1 := by
    simp only [arg, argAddr, e₆.mem, e₆.reg .esp (by decide)]; exact argE 1 (by decide)
  have e₅₇ : Keep [.esi, .edi] s₅ s₇ := (e₆.weaken (by decide)).trans (e₇.weaken (by decide))
  have esi₇ : s₇.gpr .esi = arg s 0 := by rw [e₇.reg .esi (by decide), v₆, argE 0 (by decide)]
  have edi₇ : s₇.gpr .edi = arg s 1 := by rw [v₇, a₆]
  let z := Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64)
  have hz : SchedOk z s₇ := by
    refine ⟨by rw [esi₇, e₅₇.rd, e₅₇.wr, rd₁₅, wr₁₅, hrd]; simp, by rw [esi₇]; exact fitS, ?_⟩
    rw [esi₇, e₅₇.mem]
    exact scheduleAt_congr (frame_bytes fB (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dSB) (by decide))
  have ho : OutOk ((arg s 1).setWidth 64) s₇ :=
    ⟨by rw [e₅₇.wr, wr₁₅, hwr]; simp, by rw [edi₇], by rw [edi₇]; exact fitO⟩
  refine WP.seq (WP.of_runBlock ⟨s₇, ?_, ?_⟩)
  · exact run_append (a := [_] ++ _) (run_append h₁ (run_append h₂ (run_append h₃ (run_append h₄ h₅))))
      (run_append h₆ h₇)
  refine WP.seq (WP.mono (subkeys_ok z s₇ hz ho (by rw [esi₇]; exact dSO) 52 0 rfl s₇
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun t ht => ?_)
  -- The epilogue.
  have esp_t : t.gpr .esp = s.gpr .esp := by
    rw [ht.keep.reg .esp (by decide), e₅₇.reg .esp (by decide), esp₅]
  have ft : Frame [⟨(arg s 2).setWidth 64, 16⟩, ⟨(arg s 1).setWidth 64, 104⟩] s.mem t.mem :=
    (fB.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      ((by rw [← e₅₇.mem]; exact ht.frame : Frame [⟨(arg s 1).setWidth 64, 2 * 52⟩] s₅.mem t.mem).sub
        fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  have hargsT : ⟨argAddr t 0, 12⟩ ∈ t.rd := by
    rw [ht.keep.rd, e₅₇.rd, rd₁₅]; simp only [argAddr, esp_t]; exact hargs
  obtain ⟨u₁, k₁, w₁, f₁⟩ := mov_run .eax _ _ t (arg_src (i := 2) (by decide) hargsT (by rw [esp_t]; omega))
  have eaxU : u₁.gpr .eax = arg s 2 := by
    rw [w₁]
    exact arg_frame ft (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dAB
      · exact dAO) esp_t (by omega) (by omega)
  have savedT : ∀ r d, (r, d) ∈ [(Reg.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)] →
      u₁.mem.readW ((arg s 2).setWidth 64 + BitVec.ofNat 64 d) 32 = s.gpr r := by
    intro r d hm
    have hd : d + 4 ≤ 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      omega
    rw [f₁.mem, ← saved r d hm, ← e₅₇.mem]
    exact ht.frame.readW (Offset.contains_base _ hd (by omega)) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact dOB.symm) (by decide)
  have rdAny : ∀ u : State, u.gpr .eax = arg s 2 → u.mem = u₁.mem → u.rd = u₁.rd → u.wr = u₁.wr →
      ∀ r d, (r, d) ∈ [(Reg.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)] →
        readSrc u (.mem (at_ .eax d)) = some (s.gpr r) := fun u he hm hr hw r d hm' => by
    have hd : d + 4 ≤ 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm'
      omega
    rw [load_src, he, addr_eq (by omega), hm, savedT r d hm']
    rw [he, addr_eq (by omega), hr, hw, f₁.rd, f₁.wr, ht.keep.rd, ht.keep.wr, e₅₇.rd, e₅₇.wr, rd₁₅, wr₁₅, hwr]
    exact ⟨_, by simp, Offset.contains_base _ hd (by omega)⟩
  obtain ⟨u₂, k₂, w₂, f₂⟩ := mov_run .ebx _ _ u₁ (rdAny u₁ eaxU rfl rfl rfl .ebx 0 (by simp))
  obtain ⟨u₃, k₃, w₃, f₃⟩ := mov_run .edi _ _ u₂ (rdAny u₂ (by rw [f₂.reg .eax (by decide), eaxU])
    f₂.mem f₂.rd f₂.wr .edi 8 (by simp))
  have e₁₃ : Keep [.ebx, .edi] u₁ u₃ := (f₂.weaken (by decide)).trans (f₃.weaken (by decide))
  obtain ⟨u₄, k₄, w₄, f₄⟩ := mov_run .ebp _ _ u₃ (rdAny u₃ (by rw [e₁₃.reg .eax (by decide), eaxU])
    e₁₃.mem e₁₃.rd e₁₃.wr .ebp 12 (by simp))
  have e₁₄ : Keep [.ebx, .edi, .ebp] u₁ u₄ := (e₁₃.weaken (by decide)).trans (f₄.weaken (by decide))
  obtain ⟨u₅, k₅, w₅, f₅⟩ := mov_run .esi _ _ u₄ (rdAny u₄ (by rw [e₁₄.reg .eax (by decide), eaxU])
    e₁₄.mem e₁₄.rd e₁₄.wr .esi 4 (by simp))
  have e₁₅ : Keep [.ebx, .edi, .ebp, .esi] u₁ u₅ := (e₁₄.weaken (by decide)).trans (f₅.weaken (by decide))
  have memU : u₅.mem = t.mem := by rw [e₁₅.mem, f₁.mem]
  refine WP.of_runBlock ⟨u₅, ?_, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · exact run_append (a := [_]) k₁ (run_append (a := [_]) k₂ (run_append (a := [_]) k₃
      (run_append (a := [_]) k₄ k₅)))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [f₅.reg .ebx (by decide), f₄.reg .ebx (by decide), f₃.reg .ebx (by decide), w₂]
    · exact w₅
    · rw [f₅.reg .edi (by decide), f₄.reg .edi (by decide), w₃]
    · rw [f₅.reg .ebp (by decide), w₄]
    · rw [e₁₅.reg .esp (by decide), f₁.reg .esp (by decide), esp_t]
  · rw [memU]
    exact ft.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRB
      · exact dRO) (by decide)
  · show Spec.Idea.scheduleAt u₅.mem _ = _
    rw [memU]
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn, scheduleAt_getD _ _ hn]
    exact ht.words n hn

end VG.Proof.Idea.X86

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

def invTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 16 }

theorem invTaint_wf {s : State} (h : invertContract.pre s) : VG.X86.Taint.Wf invTaint s := by
  obtain ⟨_, wr, _, _, _, ao, ab, ro, rb, _, _, _, spfit⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [invTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (n := 12) (by omega) ro ao
  · exact Taint.frame_disjoint (n := 12) (by omega) rb ab

theorem invTaint_agree {s₁ s₂ : State} (h₁ : invertContract.pre s₁) (h₂ : invertContract.pre s₂)
    (hp : invertContract.pub s₁ s₂) : VG.X86.Taint.Agree invTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, invertContract.pre s → (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    invTaint_wf h₁, invTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [invTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [invTaint] at hk
    rw [show Taint.depth invTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem invertKey_constantTime : ConstantTime isa invertContract.pre invertContract.pub invertKey :=
  VG.Taint.constantTime (A := taint) invTaint (fun _ _ h₁ h₂ hp => invTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000` at `0x4004`. -/
def invSatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x400d then 0x30 else 0
  rd := [⟨0x1000, 104⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x2000, 104⟩, ⟨0x3000, 16⟩]

theorem invertKey_verified : Verified target invertKey (Proof.Idea.invertKeyScratchContract32 abi 4) := by
  refine Verified.of_correct invert_wp invertKey_constantTime ?_
  sig_implies [Proof.Idea.invertKeyScratchContract32, Proof.Idea.invertKeyScratchSig32,
    Spec.Idea.invertKeyPost, abi, argSlots, argVal, argBytes, invertContract]
    [invSatState, arg, argAddr, Mem.readW, Mem.read] using invSatState

end VG.Proof.Idea.X86
