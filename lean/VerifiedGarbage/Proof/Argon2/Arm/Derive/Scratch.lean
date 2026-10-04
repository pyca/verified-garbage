import VerifiedGarbage.Proof.Argon2.Arm.Derive.Parameters

/-!
# Argon2 on ARMv7: the derivation's use of H′'s hash macros

The H₀ code calls the BLAKE2b functions through H′'s macros
(`Impl.Argon2.Arm.HPrime`), with `r4` pointing to `scratch` and the stack
below the locals: `ctx` gives their context (`HPrime.Ctx`), and `Inv.keeps`
the body's invariant and locals after them.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR)
open VG.Proof.MdStream.Arm (Upd Mupd)
open VG.Proof.Argon2.Arm.HPrime (Ctx Keeps)

/-- `n` bytes of `scratch` at offset `d`. -/
theorem scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 16384) :
    Region.Sub ⟨State.addr (scrP s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem mem_mem : memR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem out_mem : outR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)

/-- The 32 bytes below the locals that H′'s macros use are within the stack below them. -/
theorem stk32_call : Region.Sub (stkR (E s₀) 32) (callR s₀) :=
  VG.Proof.Argon2.Arm.stkR_sub (by decide) (by rw [E_nat hp]; have := hp.sp_lo; omega)

theorem ctx {s : State} (h : Inv s₀ s) (hb : s.gpr .r4 = scrP s₀) : Ctx (scrP s₀) (E s₀) s := by
  have := hp.scr_fits
  refine ⟨hb, h.sp, by omega, by rw [E_nat hp]; have := hp.sp_lo; omega, ?_, ?_⟩
  · rw [h.wr]
    exact (Covers.of_sub (rs' := [scrR s₀]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩)
  · exact ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha => call_stk hp a (stk32_call hp a ha)).sub_right
      (Region.sub_prefix (by decide))

/-- What H′'s macros keep keeps the body's invariant and the locals. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : Keeps (scrP s₀) (E s₀) s t) :
    Inv s₀ t ∧ ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  have sub : ∀ r ∈ [(⟨State.addr (scrP s₀), 832⟩ : Region), stkR (E s₀) 32],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨callR s₀, by simp, stk32_call hp⟩
  refine ⟨h.step k.sp (k.gpr _ (by decide)) k.rd k.wr (k.frame.sub fun r hr => ?_),
    fun d hd => lw_keep hp k.frame sub hd⟩
  obtain ⟨r', hr', hs⟩ := sub r hr
  refine ⟨r', ?_, hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

end

/-! ## The hash macros, with `Keeps` -/

section
open VG.Spec.Blake2

variable {B SP : BitVec 32} {s : State} (c : Ctx B SP s)
include c

theorem init_k {n : Nat} (hn : s.gpr .r1 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa Impl.Argon2.Arm.HPrime.init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (State.addr B) [] ∧ Keeps B SP s t :=
  (HPrime.init_ok c hn hn₁ hn₂).mono fun t ⟨r, cs, rd, wr, sp, f⟩ =>
    ⟨r, Keeps.of_call cs sp rd wr f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩⟩

theorem update_k {D : BitVec 32} {L : Nat}
    (hD : s.gpr .r9 = D) (hL : (s.gpr .r10).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa Impl.Argon2.Arm.HPrime.update s fun t =>
      Repr b h0 t.mem (State.addr B) (d ++ bytesAt s.mem (State.addr D) L) ∧ Keeps B SP s t :=
  (HPrime.update_ok c hD hL hDfit hDc hDs hDk repr hc hlen).mono fun t ⟨r, cs, rd, wr, sp, f⟩ =>
    ⟨r, Keeps.of_call cs sp rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

theorem finalize_k {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa Impl.Argon2.Arm.HPrime.finalize s fun t =>
      bytesAt t.mem (State.addr B + 768) 64 = finalHash b h0 d ∧ Keeps B SP s t :=
  (HPrime.finalize_ok c repr hc hlen).mono fun t ⟨dg, cs, rd, wr, sp, f⟩ =>
    ⟨dg, Keeps.of_call cs sp rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

end

end VG.Proof.Argon2.Arm.Derive
