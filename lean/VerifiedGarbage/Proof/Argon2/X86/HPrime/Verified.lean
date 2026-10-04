import VerifiedGarbage.Proof.Argon2.X86.HPrime.FinishCT
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Finish

section

/-!
# Argon2 H′ on x86 (32-bit): correctness

`setup_ok` saves the caller's registers and lays out the output pointer, the
bytes left and the length prefix in `scratch`; `correct` composes it with
`first_ok`, `finish_ok` and the restore of the registers.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput saved outOff leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store readW_writeW_addr contains_addr)
open VG.Proof.Sha512.X86 (ea_of)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_in_rd {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hrd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arg_frame {m : Mem} (f : Frame [scrR s₀] s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine f.readW (r := ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.arg_scr.sub_left (arg_sub hp hi)

theorem scr_in {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions s.wr (addr (scr s₀) d) 4 := by
  rw [hwr, hp.wr]
  exact ⟨scrR s₀, by simp, contains_addr hd (by decide) hp.scr_fits⟩

theorem scr_frame {m : Mem} (f : Frame [scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 16384)
    (v : BitVec 32) : Frame [scrR s₀] s₀.mem (m.writeW (addr (scr s₀) d) v) :=
  f.writeW (List.mem_singleton_self _) v (contains_addr hd (by decide) hp.scr_fits)

/-- The state after `setup`. -/
theorem setup_ok : WP isa (.block setup) s₀ fun t => Body s₀ t ∧ Out s₀ t [] ∧
    t.gpr .ebp = s₀.gpr .ebp ∧ Frame [scrR s₀] s₀.mem t.mem := by
  have hs := hp.scr_fits
  have esp : s₀.gpr .esp = esp₀ s₀ := rfl
  unfold setup
  simp only [saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_movm (ea_of esp 20) (arg_in_rd hp (i := 4) rfl (by decide)) fun t₁ u₁ => ?_
  have a₁ : t₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (ea_of a₁ 840) (scr_in hp u₁.wr (by decide)) fun t₂ u₂ => ?_
  have a₂ : t₂.gpr .eax = scr s₀ := by rw [u₂.gpr, a₁]
  refine wp_store (ea_of a₂ 844) (scr_in hp (by rw [u₂.wr, u₁.wr]) (by decide)) fun t₃ u₃ => ?_
  have a₃ : t₃.gpr .eax = scr s₀ := by rw [u₃.gpr, a₂]
  refine wp_store (ea_of a₃ 848) (scr_in hp (by rw [u₃.wr, u₂.wr, u₁.wr]) (by decide)) fun t₄ u₄ => ?_
  refine wp_mov fun t₅ u₅ => ?_
  have b₅ : t₅.gpr .ebx = scr s₀ := by rw [u₅.gpr, u₄.gpr, a₃]
  have g₅ : ∀ r, r ≠ .ebx → r ≠ .eax → t₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₅.other _ h1, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ h2]
  have rd₅ : t₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : t₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have F₅ : Frame [scrR s₀] s₀.mem t₅.mem := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact scr_frame hp (scr_frame hp (scr_frame hp (by rw [u₁.mem]; exact Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _
  refine wp_movm (ea_of (by rw [g₅ _ (by decide) (by decide)]) 12)
    (arg_in_rd hp (i := 2) (by rw [rd₅]) (by decide)) fun t₆ u₆ => ?_
  refine wp_store (ea_of (by rw [u₆.other _ (by decide), b₅]) outOff)
    (scr_in hp (by rw [u₆.wr, wr₅]) (by decide)) fun t₇ u₇ => ?_
  refine wp_movm (ea_of (by rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide)]) 16)
    (arg_in_rd hp (i := 3) (by rw [u₇.rd, u₆.rd, rd₅]) (by decide)) fun t₈ u₈ => ?_
  refine wp_store (ea_of (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) leftOff)
    (scr_in hp (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t₉ u₉ => ?_
  refine wp_store (ea_of (by rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) 832)
    (scr_in hp (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t u => WP.block_nil ?_
  -- Values.
  have v₆ : t₆.gpr .eax = op s₀ := by rw [u₆.gpr, arg_frame hp F₅ (i := 2) (by decide)]
  have F₇ : Frame [scrR s₀] s₀.mem t₇.mem := by
    rw [u₇.mem, u₆.mem]; exact scr_frame hp F₅ (by decide) _
  have v₈ : t₈.gpr .eax = arg s₀ 3 := by rw [u₈.gpr, arg_frame hp F₇ (i := 3) (by decide)]
  have rds : t.rd = s₀.rd := by rw [u.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wrs : t.wr = s₀.wr := by rw [u.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  have gt : ∀ r, r ≠ .ebx → r ≠ .eax → t.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u.gpr, u₉.gpr, u₈.other _ h2, u₇.gpr, u₆.other _ h2, g₅ _ h1 h2]
  have bt : t.gpr .ebx = scr s₀ := by
    rw [u.gpr, u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]
  have m₉ : t₉.mem = (t₇.mem.writeW (addr (scr s₀) leftOff) (arg s₀ 3)) := by
    rw [u₉.mem, u₈.mem, v₈]
  have mt : t.mem = (t₇.mem.writeW (addr (scr s₀) leftOff) (arg s₀ 3)).writeW (addr (scr s₀) 832)
      (arg s₀ 3) := by
    rw [u.mem, m₉, u₉.gpr, v₈]
  have m₇ : t₇.mem = t₅.mem.writeW (addr (scr s₀) outOff) (op s₀) := by
    rw [u₇.mem, u₆.mem, v₆]
  have Ft : Frame [scrR s₀] s₀.mem t.mem := by
    rw [mt]; exact scr_frame hp (scr_frame hp F₇ (by decide) _) (by decide) _
  -- Reads of `scratch` after the last writes.
  have R : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 16384 → e + 4 ≤ 16384 →
      (d + 4 ≤ e ∨ e + 4 ≤ d) →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e hd he h => readW_writeW_addr m v (by omega) (by omega) h
  have keep7 : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ 832 ∨ 864 ≤ d ∨ (836 ≤ d ∧ d + 4 ≤ 856)) →
      t.mem.readW (addr (scr s₀) d) 32 = t₅.mem.readW (addr (scr s₀) d) 32 := fun d hd h => by
    rw [mt, R _ _ d 832 hd (by decide) (by omega), R _ _ d leftOff hd (by decide) (by simp only [leftOff]; omega),
      m₇, R _ _ d outOff hd (by decide) (by simp only [outOff]; omega)]
  have m₅ : t₅.mem = ((s₀.mem.writeW (addr (scr s₀) 840) (s₀.gpr .ebx)).writeW (addr (scr s₀) 844)
      (s₀.gpr .esi)).writeW (addr (scr s₀) 848) (s₀.gpr .edi) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide)]
  refine ⟨⟨bt, by rw [gt _ (by decide) (by decide)], rds, wrs,
      Ft.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, fun q hq => ?_, ?_⟩,
    ⟨?_, ?_, rfl, Nat.zero_le _⟩, gt _ (by decide) (by decide), Ft⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 840 848 (by decide) (by decide) (by decide),
        R _ _ 840 844 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 844 848 (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, Mem.readW_writeW_self32]
  · rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), show P s₀ + 832 = addr (scr s₀) 832 from
      (scr_addr hp (d := 832) (by decide)).symm, mt, Mem.readW_writeW_self32, Spec.Argon2.le32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · show _ = _
    rw [mt, R _ _ outOff 832 (by decide) (by decide) (by decide),
      R _ _ outOff leftOff (by decide) (by decide) (by decide), m₇, Mem.readW_writeW_self32]
    simp
  · rw [mt, R _ _ leftOff 832 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp [ol]

theorem scr_rd {s : State} (b : Body s₀ s) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := by
  rw [b.rd, b.wr]
  exact ⟨scrR s₀, by simp [hp.wr], contains_addr hd (by decide) hp.scr_fits⟩

theorem correct : WP isa Impl.Argon2.X86.HPrime.code s₀ fun t => abiPreserved s₀ t ∧ hPrimeX86.post s₀ t := by
  have hif := hp.in_fits
  unfold Impl.Argon2.X86.HPrime.code
  refine WP.seq ((setup_ok hp).mono fun s₁ ⟨b₁, o₁, e₁, F₁⟩ => ?_)
  have hin : bytesAt s₁.mem ((inp s₀).setWidth 64) (inl s₀) = bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀) :=
    Proof.Blake2.bytesAt_congr fun i hi => F₁.bytes (R := inR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi
  refine WP.seq ((first_ok hp ⟨b₁, o₁, e₁, hin⟩).mono fun s₂ ⟨⟨b₂, o₂, e₂, _⟩, d₂⟩ => ?_)
  refine WP.seq ((finish_ok hp b₂ o₂ d₂).mono fun s₃ ⟨b₃, e₃, h₃⟩ => ?_)
  unfold restore
  refine wp_movm (ea_of b₃.ebx 848) (scr_rd hp b₃ (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (ea_of (by rw [u₄.other _ (by decide), b₃.ebx]) 844)
    (by rw [u₄.rd, u₄.wr]; exact scr_rd hp b₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_movm (ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b₃.ebx]) 840)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact scr_rd hp b₃ (by decide)) fun t u => WP.block_nil ?_
  have mt : t.mem = s₃.mem := by rw [u.mem, u₅.mem, u₄.mem]
  have sv := b₃.saved
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at sv
  obtain ⟨sb, ss, sd⟩ := sv
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u.gpr, u₅.mem, u₄.mem]; exact sb
    · rw [u.other _ (by decide), u₅.gpr, u₄.mem]; exact ss
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; exact sd
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃, e₂]
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b₃.esp]
  · rw [mt]
    refine b₃.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_out
    · exact hp.ret_scr
    · show Region.Disjoint _ ⟨(esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
      rw [Taint.sub_setWidth hp.esp_lo]
      exact Offset.base_disjoint_below _ (by omega)
  · show bytesAt t.mem _ _ = _
    rw [mt]; exact h₃

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): verified

Constant time, by relating two runs with the same public data piece by piece
(`code_ct`): the setup is checked by the taint analysis from the arguments,
`first` and `finishOutput` by their pieces; then `hPrime_verified` against the
contract with the arguments read only, and `hPrimeShared_verified` against
`Spec.Argon2.hPrimeContract`, which lets the code write them.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput chooseLength absorbInput finishInput
  absorbFixed leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm wp_cmpi contains_addr)

/-! ## The setup -/

/-- The taint analysis of the setup starts with the stack arguments public,
and the word holding `scratch` known to be the base of the second writable
region. -/
def τS : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16384], argLen := 24, argBases := [(20, 1)] }

theorem wfS {s : State} (hp : Pre s) : VG.X86.Taint.Wf τS s := by
  have ho := hp.out_fits; have hsc := hp.scr_fits; have hs := hp.esp_hi
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τS], by simpa [hp.wr] using hp.out_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.arg_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τS, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agreeS {s₁ s₂ : State} (hp₁ : Pre s₁) (hp₂ : Pre s₂) (q : Same s₁ s₂) :
    VG.X86.Taint.Agree τS s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfS hp₁, wfS hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => q.esp.symm,
    fun k h4 hk => ?_⟩
  · simp only [τS, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact q.esp.symm
  · rw [hp₁.wr, hp₂.wr]
    simp only [outR, scrR, P, op, ol, scr, q.args 2 (by decide), q.args 3 (by decide),
      q.args 4 (by decide)]
  · simp only [τS] at hk
    rw [show VG.X86.Taint.depth τS.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_hi; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_hi; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (q.args _ (by omega)).symm

theorem setup_F0 {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (F0 s₀) := by
  have hif := hp.in_fits
  refine (setup_ok hp).mono fun t ⟨b, o, e, f⟩ => ⟨b, o, e, ?_⟩
  exact Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := inR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi

theorem setup_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') :
    RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') (.block setup) fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂ :=
  ((RelCT.taint (A := taint) τS (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact agreeS hp hp' q)
    (by taint_decide)).wp fun _ _ ⟨e₁, e₂⟩ =>
      ⟨by subst e₁; exact setup_F0 hp, by subst e₂; exact setup_F0 hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## `first` -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

include hp in
theorem choose_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff)), .alu .cmp .edx (.imm 65)]) s
      fun t => t.cf = some (decide (ol s₀ < 65)) := by
  have hs := hp.scr_fits
  have hol : ol s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  refine wp_movm (VG.Proof.Sha512.X86.ea_of h.body.ebx leftOff)
    (by rw [h.body.rd, h.body.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩) fun s₁ u₁ =>
    wp_cmpi fun s₂ _ cf₂ _ => WP.block_nil ?_
  rw [cf₂, u₁.gpr, h.out.left, List.length_nil, Nat.sub_zero,
    Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl

include hp hp' q in
theorem choose_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) chooseLength fun _ _ => True := by
  unfold chooseLength
  refine RelCT.seq (rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.body.ebx, h₂.body.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun _ h => choose_blk hp h) (fun _ h => choose_blk hp' h)) ?_
  exact RelCT.ite (fun t₁ t₂ ⟨f₁, f₂⟩ => by show t₁.cf = t₂.cf; rw [f₁, f₂, q.ol_eq])
    (RelCT.nil fun _ _ _ => trivial)
    (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => nomatch h) (by taint_decide))

include hp hp' q in
theorem first_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) first fun t₁ t₂ =>
      (F0 s₀ t₁ ∧ (digest s₀ t₁).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) ∧
      (F0 s₀' t₂ ∧ (digest s₀' t₂).take (nF s₀') =
        Spec.Argon2.H (nF s₀') (Spec.Argon2.le32 (ol s₀') ++ inB s₀')) := by
  have hs := hp.scr_fits
  have hif := hp.in_fits
  have nE : nF s₀' = nF s₀ := by simp only [nF, q.ol_eq]
  unfold first
  refine RelCT.seq (rel_wp (choose_rel hp hp' q) (fun _ h => first_choose hp h)
    (fun _ h => first_choose hp' h)) ?_
  refine RelCT.seq (rel_wp ((init_rel (B := scr s₀) (E := esp₀ s₀) (n := nF s₀) (nF_pos hp)
      (Nat.min_le_right _ _)).mono (fun _ _ ⟨⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, e₁⟩, by
          have c := f₂.body.ctx hp'
          rw [q.scr_eq, q.esp] at c
          exact ⟨c, by rw [e₂, nE]⟩⟩) fun _ _ h => h)
    (fun _ h => first_init hp h) (fun _ h => first_init hp' h)) ?_
  refine RelCT.seq (rel_wp ((absorbFixed_rel (B := scr s₀) (E := esp₀ s₀) (offset := 832) (size := 4)
      (by omega) (by decide) (by decide) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
      fixed_check_832).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, pfx_cov hp f₁.body⟩, by
          have c := f₂.body.ctx hp'
          have v := pfx_cov hp' f₂.body
          simp only [P] at v
          rw [q.scr_eq, q.esp] at c; rw [q.scr_eq] at v
          exact ⟨c, v⟩⟩) fun _ _ h => h)
    (fun _ h => first_fixed hp h) (fun _ h => first_fixed hp' h)) ?_
  refine RelCT.seq (rel_wp ?_ (fun _ h => first_input hp h) (fun _ h => first_input hp' h))
    (rel_wp ?_ (fun _ h => first_finish hp h) (fun _ h => first_finish hp' h))
  · unfold absorbInput
    refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (absorbInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (absorbInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, q.inp_eq, q.inl_eq] at h; exact h)) ?_
    exact update_rel hif (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in
  · unfold finishInput
    refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (finishInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (finishInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, cntLo, cntHi, q.inl_eq] at h; exact h)) ?_
    exact finalize_rel

end

/-! ## Constant time -/

theorem code_ct : ConstantTime isa hPrimeX86.pre hPrimeX86.pub Impl.Argon2.X86.HPrime.code := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    fun s₀ s₀' t₁ t₂ r₁ r₂ ⟨h₀, h₀', hq⟩ e₁ e₂ => ?_
  have hp := pre_of s₀ h₀
  have hp' := pre_of s₀' h₀'
  have q := Same.of_pub hq
  suffices h : RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') Impl.Argon2.X86.HPrime.code fun _ _ => True from
    h s₀ s₀' t₁ t₂ r₁ r₂ ⟨rfl, rfl⟩ e₁ e₂
  unfold Impl.Argon2.X86.HPrime.code
  refine RelCT.seq (setup_rel hp hp' q) (RelCT.seq (first_rel hp hp' q)
    (RelCT.seq (R := fun t₁ t₂ => Body s₀ t₁ ∧ Body s₀' t₂) ?_ ?_))
  · exact rel_wp ((finishOutput_rel hp hp' q).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
      ⟨⟨f₁.body, f₁.out, f₁.ebp⟩, ⟨f₂.body, f₂.out, f₂.ebp⟩⟩) fun _ _ h => h)
      (fun _ ⟨f, d⟩ => (finish_ok hp f.body f.out d).mono fun _ h => h.1)
      (fun _ ⟨f, d⟩ => (finish_ok hp' f.body f.out d).mono fun _ h => h.1)
  · exact RelCT.taint (A := taint) (τr [.ebx]) (fun _ _ ⟨b₁, b₂⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [b₁.ebx, b₂.ebx, q.scr_eq]) (by taint_decide)


/-! ## A state satisfying the precondition -/

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x10000` at `0x5004`. -/
def hSatMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500D then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5016 then 1 else 0

def hSatState : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := hSatMem
  rd := [⟨0x1000, 1⟩, ⟨0x5004, 20⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩]

theorem hSat_pre : hPrimeX86.pre hSatState := by
  have a0 : arg hSatState 0 = 0x1000 := by decide
  have a1 : arg hSatState 1 = 1 := by decide
  have a2 : arg hSatState 2 = 0x2000 := by decide
  have a3 : arg hSatState 3 = 1 := by decide
  have a4 : arg hSatState 4 = 0x10000 := by decide
  have e : argAddr hSatState 0 = 0x5004 := by decide
  simp only [hPrimeX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem hPrime_verified : Verified X86.target Impl.Argon2.X86.HPrime.code hPrimeX86 :=
  ⟨fun s hs => correct (pre_of s hs), code_ct, ⟨hSatState, hSat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `hPrimeX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def hPrimeWide : Contract X86.isa :=
  { hPrimeX86 with
    pre := fun s =>
      let input : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
      let out : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 16384⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩
      s.rd = [input] ∧ s.wr = [out, scratch, args] ∧
      input.Disjoint out ∧ input.Disjoint scratch ∧ input.Disjoint args ∧ out.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      ret.Disjoint input ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
      stack.Disjoint input ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧ stack.Disjoint args ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 16384 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 20 ≤ 2 ^ 32 ∧
      (arg s 1).toNat < 2 ^ 32 ∧ 1 ≤ (arg s 3).toNat ∧ (arg s 3).toNat < 2 ^ 32 }

/-- A state satisfying `hPrimeWide.pre`. -/
def hSatWide : State :=
  { hSatState with rd := [⟨0x1000, 1⟩], wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩, ⟨0x5004, 20⟩] }

macro "hnarrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [hPrimeX86, hPrimeWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem hPrimeWide_verified : Verified X86.target Impl.Argon2.X86.HPrime.code hPrimeWide :=
  Verified.narrowTo hPrime_verified
    (fun s => [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 20⟩])
    (fun s => [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨(arg s 4).setWidth 64, 16384⟩])
    (fun s h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀,
        h₂₁, h₂₂, h₂₃, h₂₄⟩ := h
      have e : (⟨((s.gpr .esp) - BitVec.ofNat 32 60).setWidth 64, 60⟩ : Region) =
          ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩ := by rw [Taint.sub_setWidth h₂₀]; rfl
      hnarrow
      refine ⟨trivial, trivial, h₄, h₆, h₇.symm, h₈.symm, h₁₀, h₁₁, ?_, ?_, ?_, h₁₇, h₁₈, h₁₉, h₂₀,
        by omega, h₂₃⟩
      · simp only [below]; rw [e]; exact h₁₃
      · simp only [below]; rw [e]; exact h₁₄
      · simp only [below]; rw [e]; exact h₁₅)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by hnarrow at h ⊢; exact h)
    (fun _ _ _ _ h => by hnarrow; exact h)
    ⟨hSatWide, by
      have a0 : arg hSatWide 0 = 0x1000 := by decide
      have a1 : arg hSatWide 1 = 1 := by decide
      have a2 : arg hSatWide 2 = 0x2000 := by decide
      have a3 : arg hSatWide 3 = 1 := by decide
      have a4 : arg hSatWide 4 = 0x10000 := by decide
      have e : argAddr hSatWide 0 = 0x5004 := by decide
      simp only [hPrimeWide, a0, a1, a2, a3, a4, e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem hPrime_implies : hPrimeWide.Implies (Spec.Argon2.hPrimeContract X86.abi 60) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, hPrimeWide, hPrimeX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [hSatWide, hSatState, hSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using hSatWide

/-- The emitted function, against the shared contract. -/
theorem hPrimeShared_verified :
    Verified X86.target Impl.Argon2.X86.HPrime.code (Spec.Argon2.hPrimeContract X86.abi 60) :=
  hPrimeWide_verified.of_implies hPrime_implies

end VG.Proof.Argon2.X86.HPrime
