module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Pieces
public import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter search on RISC-V: addresses and copies

`scrB_ok`: `scrB rd o` puts the address of byte `o` of `scratch` in `rd`, for
`o` a multiple of 4096 below 32 KiB. `copyN_vp`: a copy (`copyN`) whose
prologue puts public addresses `S` and `D` and the count in `a0`–`a2`
(`ProOk`), into a range of `scratch` past the header and apart from the key
working space: the claims apart from the destination kept, the destination's
bytes those of the source. The prologues of the search's copies:
`pro_scr_scr`, `pro_ld_scr`, `pro_scr_big`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The stack the functions the search calls use below the stack pointer. -/
abbrev STK0 : Nat := 512

/-- A stage of the search: a state of the search with the claims, arrays
and slots `c`, from a call with the property `X`. -/
abbrev St (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := SS G STK0 σ c s ∧ X σ

theorem GP.sa_add (G : GP) (o i : Nat) : G.sa o + BitVec.ofNat 64 i = G.sa (o + i) := by
  simp only [GP.sa, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `lui`'s value for the multiples of 4096 below 32 KiB. -/
theorem luiv : ∀ h < 8, sext32 (BitVec.ofNat 20 h ++ (0 : BitVec 12)) = BitVec.ofNat 64 (4096 * h) := by
  decide

/-- `scrB rd o`: `rd := S + o`. -/
theorem scrB_ok {G : GP} {s : State} {rd : Reg} {o : Nat} (hrd : rd ≠ .s6) (h6 : s.gpr .s6 = G.scr)
    (ho : o % 4096 = 0) (h8 : o / 4096 < 8) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Keep [rd] s t → t.mem = s.mem → t.sp = s.sp → t.gpr rd = G.sa o → WP isa (.block rest) t Q) :
    WP isa (.block (scrB rd o ++ rest)) s Q := by
  simp only [scrB, List.cons_append, List.nil_append]
  refine WP.cons exec_lui ?_
  refine wp_add fun t u => ?_
  refine k t ⟨fun r hr => ?_, by rw [u.rd]; rfl, by rw [u.wr]; rfl⟩ (by rw [u.mem]; rfl) (by rw [u.sp]; rfl) ?_
  · have hr' : r ≠ rd := by simpa using hr
    rw [u.other _ hr', RegUpd.gpr_write_of_ne _ _ hr']
  · rw [u.gpr, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (Ne.symm hrd), h6, luiv _ h8,
      show 4096 * (o / 4096) = o by omega, BitVec.add_comm]

/-- A copy's prologue puts `S`, `D` and `n` in `a0`, `a1` and `a2`, changing
only those registers. -/
abbrev ProOk (F : State → State → Prop) (pro : List Instr) (S D : Addr) (n : Nat) : Prop :=
  ∀ σ s, F σ s → WP isa (.block pro) s fun t => Keep [.a0, .a1, .a2] s t ∧ t.mem = s.mem ∧ t.sp = s.sp ∧
    t.gpr .a0 = S ∧ t.gpr .a1 = D ∧ t.gpr .a2 = BitVec.ofNat 64 n

section
variable {G : GP} {STK : Nat}

/-- A copy of `n` bytes from `S` (readable, apart from the destination) into
the range `[dst, dst + n)` of `scratch`, past the header and apart from the
key working space: the claims apart from the destination kept, the
destination's bytes those at `S`. -/
theorem copyN_vp {F Q : State → State → Prop} {c : State → Cfg} {src dst : List Instr} {S : Addr} {o n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn64 : n < 2 ^ 63)
    (cert : (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6]) (.block (src ++ dst ++ ([.li .a2 n] : List Instr)))
      (VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (src ++ dst ++ ([.li .a2 n] : List Instr))))).isSome
      = true)
    (hpro : ProOk F (src ++ dst ++ ([.li .a2 n] : List Instr)) S (G.sa o) n)
    (hdo : ∀ σ s, F σ s → ClOk G (o, List.replicate n 0))
    (hSr : ∀ σ s, F σ s → (∀ i < n, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) ∧
      Mem.Sep (G.sa o) n S n)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart o n x) } t →
      Keep [.a0, .a1, .a2, .a3] s t →
      Spec.Rsa.bytesAt t.mem (G.sa o) n = Spec.Rsa.bytesAt s.mem S n → Q σ t) :
    VP F (copyN src dst n) Q := by
  let M : State → State → Prop := fun σ t => ∃ s, F σ s ∧ SS G STK σ (c σ) t ∧ Keep [.a0, .a1, .a2] s t ∧
    t.sp = s.sp ∧ t.mem = s.mem ∧ t.gpr .a0 = S ∧ t.gpr .a1 = G.sa o ∧ t.gpr .a2 = BitVec.ofNat 64 n
  refine VP.seq (G := M) (VP.pub (SS.pub hF) [] ⟨_, cert⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => WP.mono (hpro σ s hs) fun t ⟨K, m, sp, a0, a1, a2⟩ =>
      ⟨s, hs, (hF σ s hs).of_keep K m sp, K, sp, m, a0, a1, a2⟩) ?_
  refine VP.pub (G := G) (fun σ t ⟨_, _, h, _⟩ => ⟨h.gi.s6, by rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.a0, .a1, .a2]
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .a0, .a1, .a2])
      (Impl.Words.RISCV64.copyLoop .a3 .a0 .a1 .a2), by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, _, _, _, _, a0, a1, a2⟩ ⟨_, _, _, _, _, _, b0, b1, b2⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a0, b0]
      · rw [a1, b1]
      · rw [a2, b2]) fun σ t ⟨s, hs, h, K₁, sp₁, m₁, t0, t1, t2⟩ => ?_
  have gi := h.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  obtain ⟨Sr, sep⟩ := hSr σ s hs
  refine WP.sp_eq (WP.mono (copyLoop_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t hn
    (by omega) t2 (fun i hi => by rw [t0, K₁.2.1, K₁.2.2]; exact Sr i hi)
    (fun i hi => by rw [t1, GP.sa_add]; exact gi.inScr (o := o + i) (n := 1) (by omega)) (by rw [t0, t1]; exact sep))
    fun u ⟨cp, f, kp⟩ spu => ?_)
  have K : Keep [.a0, .a1, .a2, .a3] s u := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, K₁.2.1], by rw [kp.2.2, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), K₁.1 r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  refine k σ s u hs ?_ K ?_
  · refine h.of_scrs (os := [(o, n)]) (ws := [.a0, .a1, .a2, .a3]) ⟨fun r hr => kp.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
        exact ⟨hr.2.2.2, hr.1, hr.2.1, hr.2.2.1⟩), kp.2.1, kp.2.2⟩ spu (fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
      (by rw [t1] at f; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
    obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
    exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩
  · simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [← t1, cp i hi', t0, m₁]

end


/-! ## The prologues of the search's copies -/

section
variable {G : GP} {STK : Nat}

/-- `[scr .a0 x] ++ [scr .a1 y] ++ [.li .a2 n]`. -/
theorem pro_scr_scr {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {x y n : Nat} (hx : x < 2048) (hy : y < 2048) (hn : n < 2048) :
    ProOk F (([scr .a0 x] : List Instr) ++ ([scr .a1 y] : List Instr) ++ ([.li .a2 n] : List Instr)) (G.sa x) (G.sa y) n := by
  intro σ s hs
  have h6 := (hF σ s hs).gi.s6
  simp only [scr, List.cons_append, List.nil_append]
  refine wp_addi hx fun s₁ u₁ => wp_addi hy fun s₂ u₂ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₂.rd, u₁.rd], by rw [u.wr, u₂.wr, u₁.wr]⟩, by rw [u.mem, u₂.mem, u₁.mem],
    by rw [u.sp, u₂.sp, u₁.sp], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h6]
  · rw [u.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h6]

/-- `[ld .a0 f] ++ [scr .a1 y] ++ [.li .a2 n]`, the header word `f` holding `P`. -/
theorem pro_ld_scr {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {f y n : Nat} {P : Addr} (hf : f + 8 ≤ hEnd) (hf8 : f % 8 = 0) (hP : ∀ σ s, F σ s → fw s.mem G f = P)
    (hy : y < 2048) (hn : n < 2048) :
    ProOk F (([ld .a0 f] : List Instr) ++ ([scr .a1 y] : List Instr) ++ ([.li .a2 n] : List Instr)) P (G.sa y) n := by
  intro σ s hs
  have h := hF σ s hs
  simp only [scr, List.cons_append, List.nil_append]
  refine h.gi.ldV hf hf8 (hP σ s hs) fun s₁ u₁ => wp_addi hy fun s₂ u₂ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₂.rd, u₁.rd], by rw [u.wr, u₂.wr, u₁.wr]⟩, by rw [u.mem, u₂.mem, u₁.mem],
    by rw [u.sp, u₂.sp, u₁.sp], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.gi.s6]

/-- `[scr .a0 x] ++ (scrB .a1 o ++ [.addi .a1 .a1 k]) ++ [.li .a2 n]`. -/
theorem pro_scr_big {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {x o k n : Nat} (hx : x < 2048) (ho : o % 4096 = 0) (h8 : o / 4096 < 8) (hk : k < 2048) (hn : n < 2048) :
    ProOk F (([scr .a0 x] : List Instr) ++ (scrB .a1 o ++ ([.addi .a1 .a1 k] : List Instr)) ++ ([.li .a2 n] : List Instr)) (G.sa x) (G.sa (o + k)) n := by
  intro σ s hs
  have h6 := (hF σ s hs).gi.s6
  simp only [scr, List.cons_append, List.append_assoc, List.nil_append]
  refine wp_addi hx fun s₁ u₁ => ?_
  refine scrB_ok (by decide) (by rw [u₁.other _ (by decide), h6]) ho h8 fun s₂ K₂ m₂ sp₂ a₂ => ?_
  refine wp_addi hk fun s₃ u₃ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₃.rd, K₂.2.1, u₁.rd], by rw [u.wr, u₃.wr, K₂.2.2, u₁.wr]⟩,
    by rw [u.mem, u₃.mem, m₂, u₁.mem], by rw [u.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₃.other _ hr.2.1, K₂.gpr (by simpa using hr.2.1), u₁.other _ hr.1]
  · rw [u.other _ (by decide), u₃.other _ (by decide), K₂.gpr (by decide), u₁.gpr, h6]
  · rw [u.other _ (by decide), u₃.gpr, a₂, GP.sa_add]

/-- `scrB .a0 o ++ [ld .a1 f] ++ [.li .a2 n]`, the header word `f` holding `P`. -/
theorem pro_big_ld {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {o f n : Nat} {P : Addr} (ho : o % 4096 = 0) (h8 : o / 4096 < 8) (hf : f + 8 ≤ hEnd) (hf8 : f % 8 = 0)
    (hP : ∀ σ s, F σ s → fw s.mem G f = P) (hn : n < 2048) :
    ProOk F (scrB .a0 o ++ ([ld .a1 f] : List Instr) ++ ([.li .a2 n] : List Instr)) (G.sa o) P n := by
  intro σ s hs
  have h := hF σ s hs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine scrB_ok (by decide) h.gi.s6 ho h8 fun s₁ K₁ m₁ sp₁ a₁ => ?_
  have h₁ : SS G STK σ (c σ) s₁ := h.of_keep K₁ m₁ sp₁
  refine h₁.gi.ldV (v := P) hf hf8 (by rw [m₁]; exact hP σ s hs) fun s₂ u₂ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₂.rd, K₁.2.1], by rw [u.wr, u₂.wr, K₁.2.2]⟩, by rw [u.mem, u₂.mem, m₁],
    by rw [u.sp, u₂.sp, sp₁], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₂.other _ hr.2.1, K₁.gpr (by simpa using hr.1)]
  · rw [u.other _ (by decide), u₂.other _ (by decide), a₁]
  · rw [u.other _ (by decide), u₂.gpr]

end


/-- Disjoint regions are separate ranges. -/
theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x hx hy => h x (by show (x - a).toNat + 1 ≤ n; omega) (by show (x - b).toNat + 1 ≤ k; omega)

/-! ## Copies as pieces -/

section
variable {G : GP} {STK : Nat}

/-- A copy between two ranges of `scratch` below 2048, past the header, apart
from the key working space and from each other. -/
theorem copyS_vp {F Q : State → State → Prop} {c : State → Cfg} {dst src n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn2 : n < 2048) (hd2 : dst < 2048)
    (hs2 : src < 2048) (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hso : ∀ σ s, F σ s → src + n ≤ G.scrLen * 8)
    (hsep : dst + n ≤ src ∨ src + n ≤ dst)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.a0, .a1, .a2, .a3] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (G.sa src) n → Q σ t) :
    VP F (copyS dst src n) Q :=
  copyN_vp hF hn (by omega) (by kernel_rfl) (pro_scr_scr hF hs2 hd2 hn2) hdo
    (fun σ s hs => by
      have gi := (hF σ s hs).gi
      have := hso σ s hs
      refine ⟨fun i hi => by rw [GP.sa_add]; exact gi.inRdWr (o := src + i) (n := 1) (by omega), ?_⟩
      have := (hdo σ s hs).2.2; simp only [List.length_replicate] at this
      exact Offset.sep _ hsep (by omega) (by omega)) k

/-- A copy of `n` bytes from the pointer `P` in the header word `o` (readable,
apart from `scratch`) to a range of `scratch` below 2048, past the header and
apart from the key working space. -/
theorem copyIn_vp {F Q : State → State → Prop} {c : State → Cfg} {o dst n : Nat} {P : Addr}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn2 : n < 2048) (hd2 : dst < 2048)
    (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hP : ∀ σ s, F σ s → fw s.mem G o = P)
    (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hPr : ∀ σ s, F σ s → InRegions (s.rd ++ s.wr) P n ∧ (⟨P, n⟩ : Region).Disjoint G.rScr)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.a0, .a1, .a2, .a3] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem P n → Q σ t) :
    VP F (copyN [ld .a0 o] [scr .a1 dst] n) Q :=
  copyN_vp hF hn (by omega) (by kernel_rfl) (pro_ld_scr hF ho h8 hP hd2 hn2) hdo
    (fun σ s hs => by
      obtain ⟨⟨r, hr, hc⟩, hd⟩ := hPr σ s hs
      refine ⟨fun i hi => ⟨r, hr, hc.byte (by
        rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)⟩, ?_⟩
      have := (hdo σ s hs).2.2; simp only [List.length_replicate] at this
      exact sep_of_disjoint ((hd.sub_right (sw G this)).symm)) k

end

end VG.Proof.Dsa.RISCV64.PSearch
