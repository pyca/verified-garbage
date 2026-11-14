module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Env

import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on x86-64: GHASH over one block of the state or of `T`

Untrusted: everything here is checked by Lean. `ghash1 yo b o` continues
the accumulator at `St + yo` over the block at `P = b + o` (`ghash1_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator
at `Y`, the `g` bytes of working space at `W + 512` (none if it needs none)
and the data `ds` (as blocks). -/
structure GhOut (s : State) (Ctx Y W SP : Addr) (ds : List Block) (g : Nat := 256) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨W + BitVec.ofNat 64 512, g⟩, below SP 8] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {Ctx St W SP Y : Addr} {N g : Nat} {ds : List Block} (h : GhOut s Ctx Y W SP ds g s')
    (he : Env Ctx St W SP s N) : Env Ctx St W SP s' N := he.of_saved h.saved h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- The arguments of a call of `vg_ghash` for the accumulator at `St + yo`
and the `n` blocks at `P`, with `W + 512` in `r8`, and the regions they
need, for working space of `g` bytes at `W + 512`. -/
structure GhArgs (Ctx St W SP : Addr) (N yo : Nat) (P : Addr) (n g : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s N
  rdi : s.gpr .rdi = Ctx + BitVec.ofNat 64 240
  rsi : s.gpr .rsi = St + BitVec.ofNat 64 yo
  rdx : s.gpr .rdx = P
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = W + BitVec.ofNat 64 512
  n_lt : 16 * n < 2 ^ 64
  hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16 * n⟩
  hpw : (⟨P, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, g⟩
  hpk : (below SP 8).Disjoint ⟨P, 16 * n⟩
  hpr : Covers [⟨P, 16 * n⟩] (s.rd ++ s.wr)

/-- The call's arguments, with the 256 bytes of working space at `W + 512`. -/
theorem GhArgs.call {Ctx St W SP : Addr} {N yo : Nat} {P : Addr} {n : Nat} {s : State}
    (L : Lay Ctx St W SP N) (hN : 768 ≤ N) (hyo : yo = 0 ∨ yo = 16) (h : GhArgs Ctx St W SP N yo P n 256 s) :
    GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) n := by
  have he := h.env
  have hk := he.rsp
  refine ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.n_lt, L.ctx_st (by decide) (by omega_using [hyo]), L.ctx_w (by decide) hN,
    h.hpy, L.st_w (by omega_using [hyo]) (.inr ⟨by decide, hN⟩), h.hpw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact L.stk_ctx (by decide)
  · rw [hk]; exact L.stk_st (by omega_using [hyo])
  · rw [hk]; exact h.hpk
  · rw [hk]; exact L.stk_w hN
  · exact covers_cons (he.perm.ctxC (by decide)) (covers_cons h.hpr (covers_cons
      (covers_left (he.perm.stC (by omega_using [hyo]))) (covers_left (he.perm.wC hN L.nlt))))
  · exact covers_cons (he.perm.stC (by omega_using [hyo])) (he.perm.wC hN L.nlt)

/-- The call's arguments, without working space. -/
theorem GhArgs.callF {Ctx St W SP : Addr} {N yo g : Nat} {P : Addr} {n : Nat} {s : State}
    (L : Lay Ctx St W SP N) (hyo : yo = 0 ∨ yo = 16) (h : GhArgs Ctx St W SP N yo P n g s) :
    GhCallF s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 yo) P (W + BitVec.ofNat 64 512) n := by
  have he := h.env
  have hk := he.rsp
  refine ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.n_lt, L.ctx_st (by decide) (by omega_using [hyo]), h.hpy, ?_, ?_, ?_, ?_,
    covers_cons (he.perm.stC (by omega_using [hyo])) covers_nil⟩
  · rw [hk]; exact L.stk_ctx (by decide)
  · rw [hk]; exact L.stk_st (by omega_using [hyo])
  · rw [hk]; exact h.hpk
  · exact covers_cons (he.perm.ctxC (by decide)) (covers_cons h.hpr (covers_cons
      (covers_left (he.perm.stC (by omega_using [hyo]))) covers_nil))

/-- How the functions with `N` bytes at `W` call `v`'s `vg_ghash`: with `g`
bytes of working space at `W + 512` (`GhFits.base`, the 256 bytes every
implementation takes, when `W` has them), or none (`GhFits.free`, for an
implementation that never touches it, with any `W`); in one run and in two. -/
class GhFits (v : GcmImpl) (N : Nat) (g : outParam Nat) : Prop where
  fit : g = 0 ∨ 512 + g ≤ N
  ok : ∀ {Ctx St W SP : Addr} {yo : Nat} {P : Addr} {n : Nat} {s : State}, Lay Ctx St W SP N →
    (yo = 0 ∨ yo = 16) → GhArgs Ctx St W SP N yo P n g s →
    WP isa (.call v.gh.fn.name v.gh.fn.code) s (GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP (blocksAt s.mem P n) g)
  rel : ∀ {Ctx St W SP : Addr} {yo : Nat} {P : Addr} {n : Nat} {Q : State → State → Prop},
    Lay Ctx St W SP N → (yo = 0 ∨ yo = 16) →
    (∀ s₁ s₂, Q s₁ s₂ → GhArgs Ctx St W SP N yo P n g s₁ ∧ GhArgs Ctx St W SP N yo P n g s₂) →
    RelCT isa Q (.call v.gh.fn.name v.gh.fn.code) fun _ _ => True

/-- Every implementation, with the 256 bytes at `W + 512`. -/
theorem GhFits.base (v : GcmImpl) {N : Nat} (hN : 768 ≤ N) : GhFits v N 256 where
  fit := .inr (by omega_using [hN])
  ok L hyo h := WP.mono (gh_call v.gh (h.call L hN hyo)) fun _ g =>
    ⟨g.rd, g.wr, g.saved, by rw [← h.env.rsp]; exact g.frame, g.out⟩
  rel L hyo hQ := gh_rel v.gh fun s₁ s₂ h => by
    obtain ⟨a₁, a₂⟩ := hQ s₁ s₂ h
    exact ⟨_, _, _, _, _, a₁.call L hN hyo, a₂.call L hN hyo, by rw [a₁.env.rsp, a₂.env.rsp]⟩

/-- An implementation that needs no working space, with any `W`. -/
theorem GhFits.free (v : GcmImpl) (f : GhashFree v.gh.fn.code) (N : Nat) : GhFits v N 0 where
  fit := .inl rfl
  ok L hyo h := WP.mono (gh_callF v.gh f (h.callF L hyo)) fun _ g =>
    ⟨g.rd, g.wr, g.saved, g.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [h.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩, g.out⟩
  rel L hyo hQ := gh_relF v.gh f fun s₁ s₂ h => by
    obtain ⟨a₁, a₂⟩ := hQ s₁ s₂ h
    exact ⟨_, _, _, _, _, a₁.callF L hyo, a₂.callF L hyo, by rw [a₁.env.rsp, a₂.env.rsp]⟩

/-- The functions with the 2560 bytes of working space every other function takes. -/
instance GhFits.inst2560 (v : GcmImpl) : GhFits v 2560 256 := GhFits.base v (by decide)

/-- What the arguments of `ghash1 yo b o` leave, for the block at `P = b + o`. -/
structure Gh1Args (s₀ : State) (Ctx St W SP : Addr) (yo : Nat) (P : Addr) (s₁ : State) : Prop where
  rdi : s₁.gpr .rdi = Ctx + BitVec.ofNat 64 240
  rsi : s₁.gpr .rsi = St + BitVec.ofNat 64 yo
  rdx : s₁.gpr .rdx = P
  rcx : s₁.gpr .rcx = BitVec.ofNat 64 1
  r8 : s₁.gpr .r8 = W + BitVec.ofNat 64 512
  keep : ∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r
  mem : s₁.mem = s₀.mem
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr

theorem gh1Args_ok {Ctx St W SP : Addr} {N : Nat} {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env Ctx St W SP s N)
    (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) {P : Addr} (hP : s.gpr b + BitVec.ofNat 64 o = P)
    (ho : o < 2 ^ 31) :
    WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .rdx b o ++ ([.mov32 .rcx (imm 1)] : List Instr) ++
        ptr .r8 .r15 scrO)) s (Gh1Args s Ctx St W SP yo P) := by
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  rcases hb with rfl | rfl <;> rcases hyo with rfl | rfl
  all_goals
    refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg, ← hP]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok (v : GcmImpl) {Ctx St W SP : Addr} {N g : Nat} [G : GhFits v N g] (L : Lay Ctx St W SP N)
    {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env Ctx St W SP s N) (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) {P : Addr}
    (hP : s.gpr b + BitVec.ofNat 64 o = P) (ho : o < 2 ^ 31)
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, g⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16⟩) (hpr : Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 v.callees yo b o) s
      (GhOut s Ctx (St + BitVec.ofNat 64 yo) W SP [blockAt s.mem P] g) := by
  refine WP.seq (WP.mono (gh1Args_ok hyo he b o hb hP ho) fun s₁ a => ?_)
  have he₁ : Env Ctx St W SP s₁ N := he.of_saved a.keep a.rd a.wr
  refine WP.mono (G.ok L hyo (P := P) (n := 1) ⟨he₁, a.rdi, a.rsi, a.rdx, a.rcx, a.r8, by decide,
    by simpa using hpy, by simpa using hpw, by simpa using hpk,
    by rw [a.rd, a.wr]; simpa using hpr⟩) fun s' h => ?_
  exact ⟨h.rd.trans a.rd, h.wr.trans a.wr, fun r hr => (h.saved r hr).trans (a.keep r hr), a.mem ▸ h.frame,
    by rw [h.out, blocksAt_one, a.mem]⟩

/-- `ghash1 yo b o` in two runs, for the same block address `P`. -/
theorem ghash1_rel (v : GcmImpl) {Ctx St W SP : Addr} {N g : Nat} [G : GhFits v N g] (L : Lay Ctx St W SP N)
    {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    (b : Reg) (o : Nat) (hb : b = .r14 ∨ b = .r15) (ho : o < 2 ^ 31) {P : Addr}
    (hpy : (⟨St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, g⟩)
    (hpk : (below SP 8).Disjoint ⟨P, 16⟩)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block (ptr .rdi .r13 240 ++
      ptr .rsi .r14 yo ++ ptr .rdx b o ++ ([.mov32 .rcx (imm 1)] : List Instr) ++ ptr .r8 .r15 scrO)) hc).isSome = true)
    {F₁ F₂ : State → Prop}
    (hF : ∀ s, (F₁ s ∨ F₂ s) → Env Ctx St W SP s N ∧ s.gpr b + BitVec.ofNat 64 o = P ∧
      Covers [⟨P, 16⟩] (s.rd ++ s.wr)) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (ghash1 v.callees yo b o) fun _ _ => True := by
  have hA : ∀ s, (F₁ s ∨ F₂ s) → WP isa (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .rdx b o ++
      [.mov32 .rcx (imm 1)] ++ ptr .r8 .r15 scrO)) s (GhArgs Ctx St W SP N yo P 1 g) :=
    fun s hs => WP.mono (gh1Args_ok hyo (hF s hs).1 b o hb (hF s hs).2.1 ho) fun s₁ a =>
      ⟨(hF s hs).1.of_saved a.keep a.rd a.wr, a.rdi, a.rsi, a.rdx, a.rcx, a.r8, by decide, by simpa using hpy,
        by simpa using hpw, by simpa using hpk, by rw [a.rd, a.wr]; simpa using (hF s hs).2.2⟩
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) [.r13, .r14, .r15, .rsp] (fun s₁ s₂ h r hr => by
      have e₁ := (hF s₁ (.inl h.1)).1; have e₂ := (hF s₂ (.inr h.2)).1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15]
      · rw [e₁.rsp, e₂.rsp]) hc)
    (fun _ _ h => h) (fun s h => hA s (.inl h)) (fun s h => hA s (.inr h))
  exact RelCT.seq a (G.rel L hyo fun s₁ s₂ h => ⟨h.2.1, h.2.2⟩)

end VG.Proof.AesGcm.X86_64
