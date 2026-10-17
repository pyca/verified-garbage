module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on x86-64: copying the digest in a loop

`.loop (.block copyStep) .ne` copies the `4 n` bytes at `rsi` to `rdx`, four
at a time from the last, with `4 n` in `rcx`, when the two ranges are apart:
each step copies the four bytes below `rcx` and sets `ZF` iff `rcx` reaches
zero (`copyStep_ok`), and the loop's invariant is that the bytes from `rcx`
on are copied (`copyLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

theorem ea_idx (t : State) (b i : Reg) : t.ea { base := b, index := some i } = t.gpr b + t.gpr i := by
  simp [State.ea]

theorem bytesAt_copied32 (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 32)) D 4 = Spec.Sha256.bytesAt m S 4 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 4) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem sub4 {k : Nat} (hk : 4 * (k + 1) < 2 ^ 63) :
    BitVec.ofNat 64 (4 * (k + 1)) - (4 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (4 * k) := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sx32 (by decide), Offset.ofNat_sub_ofNat (by omega),
    show 4 * (k + 1) - 4 = 4 * k by omega]

/-- One step: the four bytes below `rcx` copied, and `ZF` set iff none are left. -/
theorem copyStep_ok {u : State} {S D : Addr} {k : Nat} (hc : u.gpr .rcx = BitVec.ofNat 64 (4 * (k + 1)))
    (hk : 4 * (k + 1) < 2 ^ 63) (hs : u.gpr .rsi = S) (hd : u.gpr .rdx = D)
    (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (4 * k)) 4)
    (hw : InRegions u.wr (D + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block Cfg.copyStep) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      u'.gpr .rcx = BitVec.ofNat 64 (4 * k) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → u'.gpr r = u.gpr r) ∧
      isa.eval .ne u' = some (!decide (k = 0)) ∧ u'.syms = u.syms ∧
      u'.mem = u.mem.writeW (D + BitVec.ofNat 64 (4 * k)) (u.mem.readW (S + BitVec.ofNat 64 (4 * k)) 32) := by
  have e := sub4 hk
  have hz : (BitVec.ofNat 64 (4 * k) == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · have : BitVec.ofNat 64 (4 * k) ≠ 0 := fun h' => by
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      have h₁ : (BitVec.ofNat 64 (4 * k) == 0) = false := by simpa using this
      have h₂ : decide (k = 0) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [h₁, h₂]
  apply WP.of_runBlock
  simp only [Cfg.copyStep, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.load32, State.store32, State.setReg32, ea_idx, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc, e, hs, hd, hr, hw, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r h₁ h₂ => by simp only [h₁, h₂, ite_false], ?_, rfl, ?_⟩
  · simp only [eval, RegUpd.zf_setReg, RegUpd.zf_arithFlags, Option.map_some, hz]
  · simp

/-- What holds after the steps down to `rcx = 4 (k + 1)`: the bytes from there on are copied. -/
structure CopyInv (u : State) (S D : Addr) (n k : Nat) (s : State) : Prop where
  rd : s.rd = u.rd
  wr : s.wr = u.wr
  rcx : s.gpr .rcx = BitVec.ofNat 64 (4 * (k + 1))
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = u.gpr r
  syms : s.syms = u.syms
  lt : k < n
  frame : Frame [⟨D, 4 * n⟩] u.mem s.mem
  bytes : Spec.Sha256.bytesAt s.mem (D + BitVec.ofNat 64 (4 * (k + 1))) (4 * n - 4 * (k + 1)) =
    Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (4 * (k + 1))) (4 * n - 4 * (k + 1))

/-- The loop: the `4 n` bytes at `rsi` to `rdx`, with `4 n` in `rcx`, when they are apart. -/
theorem copyLoop_ok {u : State} {S D : Addr} {n : Nat} (hn : 0 < n) (hn' : 4 * n < 2 ^ 63)
    (hsep : Region.Disjoint ⟨S, 4 * n⟩ ⟨D, 4 * n⟩) (hS : S.toNat + 4 * n ≤ 2 ^ 64) (hc : u.gpr .rcx = BitVec.ofNat 64 (4 * n)) (hs : u.gpr .rsi = S)
    (hd : u.gpr .rdx = D) (hr : ∀ i < n, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (4 * i)) 4)
    (hw : ∀ i < n, InRegions u.wr (D + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.loop (.block Cfg.copyStep) .ne) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → u'.gpr r = u.gpr r) ∧ u'.syms = u.syms ∧ Frame [⟨D, 4 * n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem D (4 * n) = Spec.Sha256.bytesAt u.mem S (4 * n) := by
  refine WP.loop (M := isa) (CopyInv u S D n) ?_ (n - 1) u
    ⟨rfl, rfl, by rw [hc]; congr 2; omega, fun _ _ _ => rfl, rfl, by omega, Frame.refl _ _, by
      rw [show 4 * n - 4 * (n - 1 + 1) = 0 by omega]; rfl⟩
  intro k s hi
  have hsi : s.gpr .rsi = S := (hi.gpr _ (by decide) (by decide)).trans hs
  have hdx : s.gpr .rdx = D := (hi.gpr _ (by decide) (by decide)).trans hd
  have hk := hi.lt
  -- The bytes of the source, unchanged.
  have hsrc : ∀ {a m : Nat}, a + m ≤ 4 * n →
      Spec.Sha256.bytesAt s.mem (S + BitVec.ofNat 64 a) m = Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 a) m :=
    fun {a m} h => bytesAt_frame hi.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep.sub_left (Offset.sub_base _ h)) (by omega)
  refine WP.mono (copyStep_ok (k := k) hi.rcx (by omega) hsi hdx (by rw [hi.rd, hi.wr]; exact hr k hk)
    (by rw [hi.wr]; exact hw k hk)) fun s' ⟨hrd, hwr, hcx, hg, hne, hsy, hm⟩ => ?_
  have hf₁ : Frame [⟨D + BitVec.ofNat 64 (4 * k), 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hfr : Frame [⟨D, 4 * n⟩] u.mem s'.mem := hi.frame.trans (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩)
  -- The bytes copied: the new word, then those from before.
  have hb : Spec.Sha256.bytesAt s'.mem (D + BitVec.ofNat 64 (4 * k)) (4 * n - 4 * k) =
      Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (4 * k)) (4 * n - 4 * k) := by
    rw [show 4 * n - 4 * k = 4 + (4 * n - 4 * (k + 1)) by omega, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add, show 4 * k + 4 = 4 * (k + 1) by omega]
    congr 1
    · rw [hm, bytesAt_copied32, hsrc (by omega)]
    · rw [← hi.bytes]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine .inl ⟨hne, hrd.trans hi.rd, hwr.trans hi.wr, fun r h₁ h₂ => (hg r h₁ h₂).trans (hi.gpr r h₁ h₂),
      hsy.trans hi.syms, hfr, ?_⟩
    have := hb
    rw [Nat.mul_zero, Nat.sub_zero, add_ofNat_zero, add_ofNat_zero] at this
    exact this
  · refine .inr ⟨by rw [hne]; simp only [decide_eq_false (Nat.pos_iff_ne_zero.mp hpos), Bool.not_false],
      k - 1, by omega, ⟨hrd.trans hi.rd, hwr.trans hi.wr, by rw [hcx]; congr 2; omega,
        fun r h₁ h₂ => (hg r h₁ h₂).trans (hi.gpr r h₁ h₂), hsy.trans hi.syms, by omega, hfr, ?_⟩⟩
    rw [show k - 1 + 1 = k by omega]
    exact hb

/-! ## Clearing the frame's secrets in a loop -/

theorem ea_idx_disp (t : State) (b i : Reg) (d : Nat) :
    t.ea { base := b, index := some i, disp := (d : Int) } = t.gpr b + t.gpr i + BitVec.ofNat 64 d := by
  simp only [State.ea, BitVec.mul_one, ofInt_nat]

theorem sub8 {k : Nat} (hk : 8 * (k + 1) < 2 ^ 63) :
    BitVec.ofNat 64 (8 * (k + 1)) - (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (8 * k) := by
  rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, sx32 (by decide), Offset.ofNat_sub_ofNat (by omega),
    show 8 * (k + 1) - 8 = 8 * k by omega]

theorem zf8 (k : Nat) (hk : k < 17) : (BitVec.ofNat 64 (8 * k) == 0) = decide (k = 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · rfl
  · have : BitVec.ofNat 64 (8 * k) ≠ 0 := fun h' => by
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    have h₁ : (BitVec.ofNat 64 (8 * k) == 0) = false := by simpa using this
    have h₂ : decide (k = 0) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [h₁, h₂]

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- One step of the wipe: the words below `rcx` of `K`, `V` and the offset,
and of the candidate, written. -/
theorem wipeStep_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {k : Nat}
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (8 * (k + 1))) (hk : k < 17) :
    WP isa (.block Cfg.wipeStep) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + 8 * k), 8⟩, ⟨L.B + BitVec.ofNat 64 (24 + 8 * k + 360), 8⟩] t.mem t'.mem ∧
      (∀ r, r ≠ .rcx → t'.gpr r = t.gpr r) ∧ t'.gpr .rcx = BitVec.ofNat 64 (8 * k) ∧
      isa.eval .ne t' = some (!decide (k = 0)) := by
  have he := L.he
  have w₁ := hc.inFrW (d := 24 + 8 * k) (n := 8) (by omega) (by omega)
  have w₂ := hc.inFrW (d := 24 + 8 * k + 360) (n := 8) (by omega) (by omega)
  refine Ctx.of_keep hL hc ?_ (by decide +kernel) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_low L (by omega)
    · exact safe_high L (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.wipeStep, fC, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.store64,
    ea_idx, ea_idx_disp, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, reduceCtorEq,
    ite_true, ite_false, hc.rsp, hcx, sub8 (k := k) (by omega), Offset.add_add, w₁, w₂, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, fun r hr => by simp only [hr, ite_false], trivial, ?_⟩
  · have c8 : ∀ a : Addr, (⟨a, 8⟩ : Region).Contains a (64 / 8) := fun a => Region.contains_self a 8
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (c8 _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c8 _)
  · simp only [eval, RegUpd.zf_setReg, RegUpd.zf_arithFlags, Option.map_some, zf8 k hk]

/-- `rdx` zero and `rcx` 136. -/
theorem wipeInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipeInit) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rax = t.gpr .rax ∧
      u.gpr .rcx = BitVec.ofNat 64 (8 * (16 + 1)) := by
  apply WP.of_runBlock
  simp only [Cfg.wipeInit, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false,
    ite_true, Option.some.injEq, exists_eq_left', zx32 (show 136 < 2 ^ 32 by decide)]
  exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv⟩

/-- The frame's secrets cleared: `K`, `V` and the offset, and the candidate. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa Cfg.wipe t fun t' => Ctx L g m₀ t' ∧ t'.gpr .rax = t.gpr .rax ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 136⟩, ⟨L.B + BitVec.ofNat 64 384, 136⟩] t.mem t'.mem := by
  have h₁ := wipeInit_ok hL hc
  refine WP.seq (WP.mono h₁ fun u ⟨hcu, hmu, hax, hcx⟩ => ?_)
  refine WP.loop (M := isa) (fun k s => Ctx L g m₀ s ∧ s.gpr .rax = t.gpr .rax ∧
      s.gpr .rcx = BitVec.ofNat 64 (8 * (k + 1)) ∧ k < 17 ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 136⟩, ⟨L.B + BitVec.ofNat 64 384, 136⟩] t.mem s.mem) ?_ 16 u
    ⟨hcu, hax, hcx, by omega, by rw [hmu]; exact Frame.refl _ _⟩
  intro k s ⟨hcs, has, hcxs, hk, hfs⟩
  refine WP.mono (wipeStep_ok hL hcs hcxs hk) fun s' ⟨hc', hf', hg', hcx', hne⟩ => ?_
  have hf : Frame [⟨L.B + BitVec.ofNat 64 24, 136⟩, ⟨L.B + BitVec.ofNat 64 384, 136⟩] t.mem s'.mem :=
    hfs.trans (hf'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ (by omega) (by omega)⟩)
  have ha : s'.gpr .rax = t.gpr .rax := (hg' _ (by decide)).trans has
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact .inl ⟨hne, hc', ha, hf⟩
  · refine .inr ⟨by rw [hne]; simp only [decide_eq_false (Nat.pos_iff_ne_zero.mp hpos), Bool.not_false],
      k - 1, by omega, hc', ha, by rw [hcx', show k - 1 + 1 = k by omega], by omega, hf⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
