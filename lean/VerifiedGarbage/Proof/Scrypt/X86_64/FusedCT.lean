import VerifiedGarbage.Proof.Scrypt.X86_64.FusedCorrect
namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)

structure Ready (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∃ prev, Words (sc s₀) (memWords s.mem prev) s
  metadata : Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) s.mem

theorem Inv.ready {s₀ s : State} {k : Nat} (h : Inv s₀ k s) : Ready s₀ k s :=
  ⟨h.rd, h.wr, ⟨_, h.words⟩, h.metadata⟩

theorem Ready.rsi {s₀ s : State} {k : Nat} (h : Ready s₀ k s) : s.gpr .rsi = sc s₀ :=
  h.words.elim fun _ hw => hw.rsi

theorem Ready.scratch {s₀ s : State} {k : Nat} (hp : Pre s₀) (h : Ready s₀ k s) :
    InRegions s.wr (sc s₀) 64 := by
  rw [h.wr, hp.wr]
  exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩

theorem half_ready {s₀ s : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀)
    (h : Ready s₀ k s) (odd : Bool) :
    WP isa (fusedHalf (if odd then 64 else 0) odd) s (Ready s₀ k) := by
  obtain ⟨prev, hw⟩ := h.words
  exact (half_ok hp hk h.rd h.wr hw h.metadata odd).mono fun _ ht =>
    ⟨ht.2.2.2.2.1.trans h.rd, ht.2.2.2.2.2.1.trans h.wr, ⟨_, ht.1⟩, ht.2.2.2.1⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem half_rel {k : Nat} (hk : k < rr s₀) (odd : Bool) :
    RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t)
      (fusedHalf (if odd then 64 else 0) odd) (fun s t => Ready s₀ k s ∧ Ready s₀' k t) := by
  let H (origin : State) (s : State) : Prop :=
    s.gpr .rax = bB origin k + BitVec.ofNat 64 (if odd then 64 else 0) ∧
    s.gpr .rdi = (if odd then yO origin k else yE origin k) ∧ s.gpr .rsi = sc origin
  have hw {origin s : State} (hp : Pre origin) (h : Ready origin k s) :
      WP isa (.block (fusedHead (if odd then 64 else 0) odd)) s (H origin) :=
    (Retained.head_ok h.rsi h.metadata (h.scratch hp) _ (by cases odd <;> simp) odd).mono
      fun _ ht => ⟨ht.rax, ht.rdi, (ht.keep _ (by decide) (by decide)).trans h.rsi⟩
  have head : RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t)
      (.block (fusedHead (if odd then 64 else 0) odd)) (fun s t => H s₀ s ∧ H s₀' t) := by
    have ct : RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t)
        (.block (fusedHead (if odd then 64 else 0) odd)) (fun _ _ => True) := by
      cases odd <;> exact RelCT.taint (A := taint) (Taint.ofRegs [.rsi])
        (fun _ _ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          rw [h.1.rsi, h.2.rsi, sc, sc, hq.r8]) (by taint_decide)
    exact (ct.wp fun _ _ h => ⟨hw hp h.1, hw hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have core : RelCT isa (fun s t => H s₀ s ∧ H s₀' t) fusedCore (fun _ _ => True) :=
    Retained.core_rel.mono (fun s t h => by
      obtain ⟨⟨a, d, si⟩, ⟨a', d', si'⟩⟩ := h
      rw [a, a', d, d', si, si']
      simp only [bB, bP, yO, yE, yP, sc, hq.rdi, hq.rdx, hq.r8, hq.rr, and_self])
      (fun _ _ h => h)
  exact ((head.seq core).wp fun _ _ h =>
    ⟨half_ready hp hk h.1 odd, half_ready hp' (hq.rr ▸ hk) h.2 odd⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel {k : Nat} (hk : k < rr s₀) :
    RelCT isa (fun s t => Inv s₀ k s ∧ Inv s₀' k t) fusedBody fun s t =>
      (Inv s₀ (k + 1) s ∧ s.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0)) ∧
      (Inv s₀' (k + 1) t ∧ t.zf = some (BitVec.ofNat 64 (rr s₀' - k) - 1 == 0)) := by
  have tail : RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t) (.block fusedTail) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rsi]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      rw [h.1.rsi, h.2.rsi, sc, sc, hq.r8]) (by taint_decide)
  have ct := ((half_rel hp hp' hq hk false).seq ((half_rel hp hp' hq hk true).seq tail)).mono
    (P' := fun s t => Inv s₀ k s ∧ Inv s₀' k t) (fun _ _ h => ⟨h.1.ready, h.2.ready⟩) (fun _ _ h => h)
  exact (ct.wp fun _ _ h => ⟨body_ok hp hk h.1, body_ok hp' (hq.rr ▸ hk) h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel :
    RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.loop fusedBody .ne) fun s s' =>
      Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := fusedBody) (c := .ne)
    (Q := fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s')
    (fun n s s' => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s ∧ Inv s₀' k s') (fun n => by
      intro s s' t t' u u' ⟨k, hn, hk, h, h'⟩ e e'
      have hk' : k < rr s₀' := hq.rr ▸ hk
      obtain ⟨ht, ⟨i, z⟩, ⟨i', z'⟩⟩ := body_rel hp hp' hq hk _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_ne hp hk z, eval_ne hp' hk' z', ← hq.rr]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : k + 1 = rr s₀ := by simpa using hf
        exact ⟨hl ▸ i, hl ▸ i'⟩
      · have hl : k + 1 ≠ rr s₀ := by simpa using ht'
        exact ⟨rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, i, i'⟩) (rr s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, hp.pos, h.1, h.2⟩) fun _ _ h => h

theorem blockMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') blockMixFused fun _ _ => True := by
  unfold blockMixFused
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (bmPrologue ++ fusedSetup))
      fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.r8
        · exact hq.rsp) (c := .block (bmPrologue ++ fusedSetup)) (by taint_decide)).wp
      (F₁ := Inv s₀ 0) (F₂ := Inv s₀' 0) fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s') (.block (bmSaved.map fun (r, d) => .mov r (.mem (at_ .rsi d))))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rsi]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.words.rsi, h.2.words.rsi, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq ((loop_rel hp hp' hq).seq epi)

end
end VG.Proof.Scrypt.X86_64.BlockMix.Fused
