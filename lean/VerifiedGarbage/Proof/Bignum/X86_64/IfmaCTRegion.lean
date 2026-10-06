import VerifiedGarbage.Proof.Bignum.X86_64.IfmaRegion
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub

/-!
# RSA with AVX512_IFMA on x86-64: constant time, a prime's region

`region p` is `k1` (a copy and `doubles`, in the prime's workspace, whose
`-p⁻¹` is secret: `doublesW_ct`), then blocks that convert arrays into the
vector layout and store `k₀`, zeros, the last multiplier and the exponent.
Those blocks read pointers from the headers and `n`'s slots (`TCtx`), which
are the same in two runs with the same public data: each block is checked
by the taint analysis after its loads (`ct_split`), whose results
correctness gives. `region_ct`: `region p` is constant time for
`region_ok`'s hypotheses (`RegPre`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-! ## Helpers -/

/-- A block whose first instructions load what the rest's addresses need. -/
theorem ct_split {α : Type} {Φ Ψ : α → State → Prop} (l₁ l₂ : List Instr) (rs₁ rs₂ : List Reg)
    (hp₁ : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₁ : (taint.check (Taint.ofRegs rs₁) (.block l₁) hc₁).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block l₁) s (Ψ a)) (hp₂ : Pins Ψ rs₂) {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₂ : (taint.check (Taint.ofRegs rs₂) (.block l₂) hc₂).isSome = true) :
    RelCT isa (Two Φ) (.block (l₁ ++ l₂)) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_piece rs₁ hp₁ h₁ hw) (two_taint rs₂ hp₂ h₂))

/-- Pins from equalities to functions of the public data. -/
theorem pins_eqs {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs := pins_of f h

/-! ## `doubles` in a prime's workspace -/

/-- `double` leaks the same in runs with the same working space (whatever `-m⁻¹`). -/
theorem doubleW_ct {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodW) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := fun (L : Ws) t => DblHeadL mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩ t) _ pins_goodW h
      fun L s ⟨minv, hg, hZ⟩ => dblHead_ok (L := ⟨L.B, L.Z, L.w, minv⟩) ⟨hg, hZ⟩ hmo hacc htmp ho)
    (two_taint _ (fun L s₁ s₂ h₁ h₂ => pins_dblHead mo acc tmp o _ s₁ s₂ h₁ h₂) (by taint_decide))

/-- What `doubles` keeps after `j` doublings, for some `-m⁻¹`. -/
def DblsAtW (mo acc tmp o sl : Nat) (p : Ws × Nat) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (minv : BitVec 64) (O N : Nat), DblsInv σ p.1.B p.1.Z p.1.w minv mo acc tmp o sl p.2 O N j t ∧
    slot p.1.w 8 ≤ p.1.Z ∧ 2 ≤ p.1.w ∧ p.1.w < 2 ^ 31 ∧ p.2 < 2 ^ 31 ∧ 0 < N

/-- What `doubles` needs: the working space, the count in `rcx`, and `[o] < [mo]`. -/
def DblPreW (mo o : Nat) (p : Ws × Nat) (s : State) : Prop :=
  GoodW p.1 s ∧ 2 ≤ p.1.w ∧ p.1.w < 2 ^ 31 ∧ 1 ≤ p.2 ∧ p.2 < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.2 ∧
    wv s.mem p.1.B (slot p.1.w o) p.1.w < wv s.mem p.1.B (slot p.1.w mo) p.1.w

/-- `doubles` leaks the same in runs with the same working space and count. -/
theorem doublesW_ct {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two (DblPreW mo o)) (doubles mo acc tmp o sl) fun _ _ => True := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.2 ∧ DblsAtW mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_goodW p.1 s₁ s₂ h₁.1 h₂.1) h' ?_) ?_
  · rintro p s ⟨⟨minv, hg, hZ⟩, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.scr hg.rdi hg.hdr hZ hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega, s, minv, _, _, hI, hZ, hw, hw', hc', by omega⟩
  refine (two_loop (Φ := DblsAtW mo acc tmp o sl) (Ψ := fun _ _ => True) (fun p => p.2) ?_ ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : (Ws × Nat) × Nat) s => GoodW q.1.1 s)
      (two_map (·.1.1) (fun _ _ h => ?_) (doubleW_ct hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_goodW q.1.1 s₁ s₂ h₁ h₂) h'')
    · obtain ⟨_, σ, minv, O, N, hI, hZ, _⟩ := h
      exact ⟨minv, ⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩
    rintro ⟨p, j⟩ s ⟨hj, σ, minv, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨minv, ⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, minv, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, minv, O, N, hI', hZ, hw, hw', hc', hN0⟩,
        fun _ => trivial⟩

/-! ## The region's public data and what its blocks read -/

/-- The public data of a region: `n`'s workspace `B` (of `Z` bytes), the
prime's at `off B o`, the area at `off B a`, `n`'s slots of the exponent's
pointer `ep` and length `L`. -/
structure RegPub where
  B : Addr
  Z : Nat
  o : Nat
  a : Nat
  ep : Addr
  L : Nat

/-- The prime's workspace. -/
abbrev RegPub.pw (q : RegPub) : Ws := ⟨off q.B q.o, slot 16 8, 16⟩

/-- The layout of region `p`. -/
def RegPub.Ok (q : RegPub) (p sp sl : Nat) : Prop :=
  q.o + slot 16 8 + tabBytes 16 ≤ q.a ∧ q.a + 2 * D + 8 ≤ q.Z ∧ p < 2 ∧ sp < 32 ∧ sl < 32 ∧ 1 ≤ q.L ∧ q.L ≤ 128

/-- What the region's blocks read (`TCtx`). -/
def RT (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  q.Ok p sp sl ∧ ∃ (mx : BitVec 64) (eb : List Byte), TCtx s q.B q.Z q.o q.a mx sp sl q.ep eb ∧ eb.length = q.L

theorem RT.of_frm {p sp sl : Nat} {q : RegPub} {s t : State} (h : RT p sp sl q s) {rs : List (Nat × Nat)}
    (hf : Frm q.B rs s.mem t.mem) (hr : ∀ r ∈ rs, q.a ≤ r.1 ∧ r.1 + r.2 ≤ q.Z)
    (k : Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] s t) : RT p sp sl q t := by
  obtain ⟨ok, mx, eb, c, hl⟩ := h
  have hok := ok
  obtain ⟨hoa, haZ, _, hsp, hsl, _⟩ := ok
  exact ⟨hok, mx, eb, c.of_frm hf hr hoa (by omega) hsp hsl k, hl⟩

theorem RT.rdi {p sp sl : Nat} {q : RegPub} {s : State} (h : RT p sp sl q s) : s.gpr .rdi = off q.B q.o :=
  let ⟨_, _, _, c, _⟩ := h; c.rdi

theorem pins_rt {p sp sl : Nat} {Φ : RegPub → State → Prop} (h : ∀ q s, Φ q s → RT p sp sl q s) : Pins Φ [.rdi] :=
  pins_eqs (fun q _ => off q.B q.o) fun q s hs r hr => by
    rw [List.mem_singleton.mp hr]; exact (h q s hs).rdi

theorem ofs_bound {p : Nat} (hp : p < 2) : D * p ≤ 3712 := by
  have : D = 3712 := rfl
  rcases AmmSym.D_mul hp with h | h <;> omega

/-! ## The blocks -/

theorem arr52_eq (p j c : Nat) : CrtIfma.arr52 p j c =
    ([.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma))] : List Instr) ++
      (([.alu .add .r11 (.imm (BitVec.ofNat 32 (D * p + c))), .movImm64 .r12 mask52] : List Instr) ++
        CrtIfma.to52) := rfl

/-- `arr52`'s loads: the array's and the area's addresses. -/
theorem arrLd_ok {p j sp sl : Nat} (hj : j < 8) {q : RegPub} {s : State} (h : RT p sp sl q s) :
    WP isa (.block [.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma))]) s fun t =>
      t.gpr .rsi = off (off q.B q.o) (slot 16 j) ∧ t.gpr .r11 = off q.B q.a := by
  obtain ⟨⟨hoa, haZ, -⟩, mx, eb, c, -⟩ := h
  have hn := c.scr.nowrap
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hH : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off q.B q.o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact c.scr.ld (by have := hdr_lt_slot 16 8 hi; omega)
  refine WP.mono (WP.keep [.rsi, .r11] (Q := fun t => t.gpr .rsi = off (off q.B q.o) (slot 16 j) ∧
    t.gpr .r11 = off q.B q.a) (by
      xrun [State.ea, hdr, c.rdi, hdrOff, hH _ (show sArr j < 32 by unfold sArr; omega), hH sIfma (by decide)]
      exact ⟨c.hdr.harr j hj, c.ia⟩) rfl) fun t h => h.1

theorem arr52_rt {p j c sp sl : Nat} (hc : c + 160 ≤ D) (hj : j < 8) {q : RegPub} {s : State} (h : RT p sp sl q s) :
    WP isa (.block (CrtIfma.arr52 p j c)) s fun t => RT p sp sl q t ∧ t.gpr .r12 = mask52 := by
  have hRT := h
  obtain ⟨⟨hoa, haZ, hp, -⟩, mx, eb, c', -⟩ := h
  have := ofs_bound hp
  have hD : D = 3712 := rfl
  exact WP.mono (arr52r_ok c'.scr c'.rdi c'.hdr c'.ia hoa haZ hp hc hj) fun t ⟨_, f, k, h12, _⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k, h12⟩

/-- `arr52` is constant time, given that the taint analysis checks the rest after its loads. -/
theorem arr52_ct {p j c sp sl : Nat} (hj : j < 8) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block ([.mov .rsi (.mem (hdr (sArr j))),
      .mov .r11 (.mem (hdr sIfma))] : List Instr)) hc₁).isSome = true) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rsi, .r11]) (.block (([.alu .add .r11 (.imm (BitVec.ofNat 32 (D * p + c))),
      .movImm64 .r12 mask52] : List Instr) ++ CrtIfma.to52)) hc).isSome = true) :
    RelCT isa (Two (RT p sp sl)) (.block (CrtIfma.arr52 p j c)) fun _ _ => True := by
  rw [arr52_eq]
  exact ct_split _ _ [.rdi] [.rsi, .r11] (pins_rt fun _ _ h => h) hT₁
    (fun _ _ h => arrLd_ok hj h)
    (pins_eqs (fun q r => if r = .rsi then off (off q.B q.o) (slot 16 j) else off q.B q.a) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) hT

theorem k0St_eq (p : Nat) : CrtIfma.k0St p = ([.mov .r11 (.mem (hdr sIfma))] : List Instr) ++
    (([.alu .add .r11 (.imm (BitVec.ofNat 32 (D * p))), .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] :
      List Instr) ++ (List.range 4).map (fun l => .store (CrtIfma.at_ .r11 (oK0 + 8 * l)) .rax)) := rfl

theorem k0St_rt {p sp sl : Nat} {q : RegPub} {s : State} (h : RT p sp sl q s ∧ s.gpr .r12 = mask52) :
    WP isa (.block (CrtIfma.k0St p)) s fun t => RT p sp sl q t ∧ t.gpr .r11 = off (off q.B q.a) (D * p) := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h12⟩ := h
  have := ofs_bound hp
  have hD : D = 3712 := rfl
  exact WP.mono (k0r_ok c.scr c.rdi c.hdr c.ia hoa haZ hp h12) fun t ⟨_, f, r11, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [oK0]; omega) (k.mono (by simp)), r11⟩

theorem k0St_ct (p : Nat) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .r11]) (.block (([.alu .add .r11 (.imm (BitVec.ofNat 32 (D * p))),
      .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
      (List.range 4).map (fun l => .store (CrtIfma.at_ .r11 (oK0 + 8 * l)) .rax))) hc).isSome = true) :
    RelCT isa (Two fun q s => RT p sp sl q s ∧ s.gpr .r12 = mask52) (.block (CrtIfma.k0St p)) fun _ _ => True := by
  rw [k0St_eq]
  refine ct_split (Ψ := fun q t => t.gpr .rdi = off q.B q.o ∧ t.gpr .r11 = off q.B q.a) _ _ [.rdi] [.rdi, .r11]
    (pins_rt fun _ _ h => h.1) (by taint_decide) (fun q s h => ?_)
    (pins_eqs (fun q r => if r = .rdi then off q.B q.o else off q.B q.a) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) hT
  obtain ⟨⟨⟨hoa, haZ, -⟩, mx, eb, c, -⟩, -⟩ := h
  have hn := c.scr.nowrap
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT' : tabBytes 16 = 2304 := rfl
  have hH : InRegions (s.rd ++ s.wr) (off (off q.B q.o) (8 * sIfma)) 8 := by
    rw [off_off]; exact c.scr.ld (by unfold sIfma sFn; omega)
  exact WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = off q.B q.a) (by
    xrun [State.ea, hdr, c.rdi, hdrOff, hH]; exact c.ia) rfl) fun t ⟨h11, k⟩ =>
      ⟨(k.gpr (by decide)).trans c.rdi, h11⟩

theorem eZero_rt {p sp sl : Nat} {q : RegPub} {s : State} (h : RT p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * p)) :
    WP isa (.block CrtIfma.eZero) s fun t =>
      RT p sp sl q t ∧ t.gpr .r11 = off (off q.B q.a) (D * p) ∧ t.gpr .rax = 0 := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h11⟩ := h
  have := ofs_bound hp
  have hD : D = 3712 := rfl
  exact WP.mono (eZr_ok c.scr haZ hp h11) fun t ⟨_, f, ra, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [oE]; omega) (k.mono (by simp)),
      (k.gpr (by decide)).trans h11, ra⟩

theorem eZero_ct (p : Nat) {sp sl : Nat} :
    RelCT isa (Two fun q s => RT p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * p)) (.block CrtIfma.eZero)
      fun _ _ => True :=
  two_taint [.r11] (pins_eqs (fun q _ => off (off q.B q.a) (D * p))
    fun q s (h : RT p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * p)) r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2) (by taint_decide)

theorem finOne_rt {sp sl : Nat} {q : RegPub} {s : State}
    (h : RT 1 sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * 1) ∧ s.gpr .rax = 0) :
    WP isa (.block CrtIfma.finOne) s fun t => RT 1 sp sl q t ∧ t.gpr .r11 = off (off q.B q.a) (D * 1) := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h11, ha⟩ := h
  have hD : D = 3712 := rfl
  exact WP.mono (finr_ok c.scr haZ h11 ha) fun t ⟨_, f, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [oFin]; omega) (k.mono (by simp)),
      (k.gpr (by decide)).trans h11⟩

theorem finOne_ct {sp sl : Nat} :
    RelCT isa (Two fun q s => RT 1 sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * 1) ∧ s.gpr .rax = 0)
      (.block CrtIfma.finOne) fun _ _ => True :=
  two_taint [.r11] (pins_eqs (fun q _ => off (off q.B q.a) (D * 1))
    fun q s (h : RT 1 sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * 1) ∧ s.gpr .rax = 0) r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2.1) (by taint_decide)

/-! ## The exponent's copy -/

/-- After `eCopy`'s first block: the pointer, the length and the destination. -/
def ECp (p : Nat) (q : RegPub) (t : State) : Prop :=
  t.gpr .rsi = q.ep ∧ t.gpr .rcx = BitVec.ofNat 64 q.L ∧
    t.gpr .r11 = off (off (off q.B q.a) (D * p)) (oE + 128 - q.L)

theorem eBlk_ok {p sp sl : Nat} {q : RegPub} {s : State}
    (h : RT p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * p)) :
    WP isa (.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax sp)), .mov .rcx (.mem (ws .rax sl)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (oE + 128))), .alu .sub .r11 (.reg .rcx)]) s (ECp p q) := by
  obtain ⟨⟨⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩, mx, eb, c, hl⟩, h11⟩ := h
  have hn := c.scr.nowrap
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hlk : InRegions (s.rd ++ s.wr) (off (off q.B q.o) (8 * sLink)) 8 := by
    rw [off_off]; exact c.scr.ld (by unfold sLink sFn; omega)
  have hlv₁ : s.mem.readW (off (off q.B q.o) (8 * sLink)) 64 = q.B := c.lk
  have hp' : InRegions (s.rd ++ s.wr) (off q.B (8 * sp)) 8 := c.scr.ld (by omega)
  have hl' : InRegions (s.rd ++ s.wr) (off q.B (8 * sl)) 8 := c.scr.ld (by omega)
  have hlv' : word s.mem q.B (8 * sl) = BitVec.ofNat 64 q.L := by rw [← hl]; exact c.lv
  refine WP.mono (WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t => t.gpr .rsi = q.ep ∧
    t.gpr .rcx = BitVec.ofNat 64 q.L ∧ t.gpr .r11 = off (off (off q.B q.a) (D * p)) (oE + 128 - q.L)) (by
    xrun [State.ea, hdr, ws, c.rdi, hdrOff, hlk, hlv₁, hp', hl',
      AmmSym.se_ofNat (show oE + 128 < 2 ^ 31 by simp only [oE]; omega)]
    and_intros
    · exact c.pv
    · exact hlv'
    rw [show s.mem.readW (off q.B (8 * sl)) 64 = BitVec.ofNat 64 q.L from hlv', h11,
      VG.Offset.add_ofNat_sub _ (by simp only [oE]; omega)]) rfl) fun t h => h.1

/-- `eCopy` is constant time, given that the taint analysis checks its loads
from `n`'s workspace. -/
theorem eCopy_ct {p sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two fun q s => RT p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (D * p))
      (seqs (CrtIfma.eCopy sp sl)) fun _ _ => True := by
  show RelCT isa _ (.seq (.block (([.mov .rax (.mem (hdr sLink))] : List Instr) ++
    (([.mov .rsi (.mem (ws .rax sp)), .mov .rcx (.mem (ws .rax sl))] : List Instr) ++
      ([.alu .add .r11 (.imm (BitVec.ofNat 32 (oE + 128))), .alu .sub .r11 (.reg .rcx)] : List Instr)))) _) _
  refine RelCT.seq (two_post (Ψ := ECp p) ?_ fun q s h => eBlk_ok h)
    (two_taint [.rsi, .rcx, .r11] (pins_eqs (fun q r => if r = .rsi then q.ep else if r = .rcx then
      BitVec.ofNat 64 q.L else off (off (off q.B q.a) (D * p)) (oE + 128 - q.L)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => (RT p sp sl q t ∧
      t.gpr .r11 = off (off q.B q.a) (D * p)) ∧ t.gpr .rax = q.B) [.rdi]
    (pins_rt fun _ _ h => h.1) (by taint_decide) ?_) (RelCT.block_append (RelCT.seq (two_piece
      (Ψ := fun q t => t.gpr .rcx = BitVec.ofNat 64 q.L ∧ t.gpr .r11 = off (off q.B q.a) (D * p)) [.rax]
      (pins_eqs (fun q _ => q.B) fun q s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2) hT ?_)
    (two_taint [.rcx, .r11] (pins_eqs (fun q r => if r = .rcx then BitVec.ofNat 64 q.L else
      off (off q.B q.a) (D * p)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide)))))
  · rintro q s ⟨hRT, h11⟩
    have hRT' := hRT
    obtain ⟨⟨hoa, haZ, -⟩, mx, eb, c, -⟩ := hRT'
    have hn := c.scr.nowrap
    have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
    have hT' : tabBytes 16 = 2304 := rfl
    have hlk : InRegions (s.rd ++ s.wr) (off (off q.B q.o) (8 * sLink)) 8 := by
      rw [off_off]; exact c.scr.ld (by unfold sLink sFn; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = q.B ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, c.rdi, hdrOff, hlk]; exact c.lk) rfl) fun t ⟨⟨ha, hm⟩, k⟩ =>
        ⟨⟨hRT.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (k.mono (by simp)),
          (k.gpr (by decide)).trans h11⟩, ha⟩
  · rintro q s ⟨⟨hRT, h11⟩, ha⟩
    obtain ⟨⟨hoa, haZ, hp, hsp, hsl, -⟩, mx, eb, c, hl⟩ := hRT
    have hn := c.scr.nowrap
    have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
    have hp' : InRegions (s.rd ++ s.wr) (off q.B (8 * sp)) 8 := c.scr.ld (by omega)
    have hl' : InRegions (s.rd ++ s.wr) (off q.B (8 * sl)) 8 := c.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 q.L) (by
      xrun [State.ea, ws, ha, hdrOff, hp', hl']; rw [← hl]; exact c.lv) rfl) fun t ⟨hcx, k⟩ =>
        ⟨hcx, (k.gpr (by decide)).trans h11⟩

/-! ## `k1`, and the region -/

/-- `region_ok`'s hypotheses. -/
def RegPre (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  q.Ok p sp sl ∧ ∃ (w : Nat) (mx : BitVec 64) (X : Nat) (eb : List Byte), SubCtx s q.B q.Z q.o w 16 mx ∧
    word s.mem (off q.B q.o) (8 * sIfma) = off q.B q.a ∧ wv s.mem (off q.B q.o) (slot 16 Public.aN) 16 = X ∧
    wv s.mem (off q.B q.o) (slot 16 Public.aY) 16 < X ∧ word s.mem q.B (8 * sp) = q.ep ∧
    word s.mem q.B (8 * sl) = BitVec.ofNat 64 eb.length ∧ Src s q.B q.Z q.ep eb ∧ eb.length = q.L

/-- Before `doubles`. -/
def K2 (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  DblPreW Public.aN aT (q.pw, 32) s ∧
    WP isa (doubles Public.aN Public.aAcc Public.aTmp aT CrtIfma.sCtr) s (RT p sp sl q)

/-- Before `doubles`' count. -/
def K1 (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  s.gpr .rdi = off q.B q.o ∧ WP isa (.block [.mov32 .rcx (.imm 32)]) s (K2 p sp sl q)

/-- Before `k1`. -/
def K0 (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  GoodW q.pw s ∧ WP isa (seqs (copyArr aT Public.aY)) s (K1 p sp sl q)

/-- `region_ok`'s hypotheses give `K0`, as `k1_ok` runs `k1`. -/
theorem k1_chain {p sp sl : Nat} {q : RegPub} {s : State} (h : RegPre p sp sl q s) : K0 p sp sl q s := by
  obtain ⟨ok, w, mx, X, eb, hc, hia, hN, hY, hpv, hlv, he, hl⟩ := h
  have hok := ok
  obtain ⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩ := ok
  have hn := hc.scr.nowrap
  have hD : D = 3712 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hg := hc.good
  have lT := slot_le (w := 16) (show aT < 8 by decide)
  have lN := slot_le (w := 16) (show Public.aN < 8 by decide)
  have sTN := slot_sep (w := 16) (show aT ≠ Public.aN by decide)
  have hk1 : ∀ r ∈ k1Ranges 16, r.1 + r.2 ≤ slot 16 8 := by
    have := slot_le (w := 16) (show Public.aAcc < 8 by decide)
    have := slot_le (w := 16) (show Public.aTmp < 8 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [CrtIfma.sCtr, sFn] <;> omega
  refine ⟨⟨mx, hg, Nat.le_refl _⟩, WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega) (by omega) (o := aT)
    (a := Public.aY) (by decide) (by decide) (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_⟩
  have hg₁ := hg.of_outsideArr ho₁ k₁
  have hN₁ : wv s₁.mem (off q.B q.o) (slot 16 Public.aN) 16 = X := by rw [ho₁.wv (by omega) (by omega)]; exact hN
  refine ⟨hg₁.rdi, WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 32 ∧ t.mem = s₁.mem) (by
    xrun; and_intros) rfl) fun s₂ ⟨⟨cx₂, me₂⟩, k₂⟩ => ?_⟩
  have hg₂ : Good s₂ (off q.B q.o) (slot 16 8) 16 mx :=
    ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [me₂]; exact hg₁.hdr⟩
  refine ⟨⟨⟨mx, hg₂, Nat.le_refl _⟩, show 2 ≤ 16 by decide, show 16 < 2 ^ 31 by decide, show 1 ≤ 32 by decide,
    show 32 < 2 ^ 31 by decide, cx₂,
    by rw [me₂, hv₁, hN₁]; exact hY⟩, ?_⟩
  refine WP.mono (doubles_ok hg₂.scr hg₂.rdi hg₂.hdr (Nat.le_refl _) (by decide) (by decide) (mo := Public.aN)
    (acc := Public.aAcc) (tmp := Public.aTmp) (o := aT) (sl := CrtIfma.sCtr) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (c := 32) (by decide) (by decide) cx₂ (by rw [me₂, hv₁, hN₁]; exact hY)) fun t ⟨_, hf, hH, k⟩ => ?_
  have fW : Frm (off q.B q.o) (k1Ranges 16) s.mem t.mem :=
    (Frm.of_outside (ho₁.mono (o' := slot 16 aT) (n' := 8 * (16 + 2)) (Nat.le_refl _) (by omega))
      (by simp [k1Ranges])).trans (by rw [← me₂]; exact hf)
  have fB : Frm q.B (shiftRanges q.o (k1Ranges 16)) s.mem t.mem :=
    fW.rebase (by omega) fun r hr => by have := hk1 r hr; omega
  have kk := (k₁.trans k₂).trans k
  have hia' : word t.mem (off q.B q.o) (8 * sIfma) = off q.B q.a := by
    rw [fW.word_eq (fun r hr => by
      have := hdr_lt_slot 16 Public.aAcc (show sIfma < 32 by decide)
      have := hdr_lt_slot 16 Public.aTmp (show sIfma < 32 by decide)
      have := hdr_lt_slot 16 aT (show sIfma < 32 by decide)
      simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [CrtIfma.sCtr, sIfma, sFn] at * <;> omega)
      (by unfold sIfma sFn; omega)]
    exact hia
  exact ⟨hok, mx, eb, TCtx.of_regionA hc hoa haZ hp hsp hsl hpv hlv he
    (fB.mono fun r hr => List.mem_append_left _ hr) kk.2.2 kk.2.1 ((kk.gpr (by decide)).trans hc.rdi) hH hia', hl⟩

/-- A piece, then the rest of a list. -/
theorem ct_cons {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} {cs : List (Prog isa)} (hcs : cs ≠ [])
    (hc : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a))
    (hr : RelCT isa (Two Ψ) (seqs cs) fun _ _ => True) : RelCT isa (Two Φ) (seqs (c :: cs)) fun _ _ => True := by
  match cs, hcs with
  | _ :: _, _ => exact ct_step id (fun _ _ h => h) hw hc hr

theorem k1_ct {p sp sl : Nat} {rest : List (Prog isa)} (hr0 : rest ≠ [])
    (hr : RelCT isa (Two (RT p sp sl)) (seqs rest) fun _ _ => True) :
    RelCT isa (Two (RegPre p sp sl)) (seqs (CrtIfma.k1 ++ rest)) fun _ _ => True := by
  refine two_map id (fun _ _ h => k1_chain h) ?_
  simp only [CrtIfma.k1, List.append_assoc, List.cons_append, List.nil_append]
  refine ct_steps (by simp [copyArr]) (by simp) RegPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_taint [.rdi] (pins_eqs (fun q _ => off q.B q.o)
    fun q s (h : K1 p sp sl q s) r hr => by rw [List.mem_singleton.mp hr]; exact h.1) (by taint_decide))
    (fun _ _ h => h.2) ?_
  exact ct_cons hr0 (two_map (fun q : RegPub => (q.pw, 32)) (fun _ _ h => h.1) (doublesW_ct (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) (fun _ _ h => h.2) hr

/-- `p`'s region is constant time. -/
theorem region0_ct {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two (RegPre 0 sp sl)) (seqs (CrtIfma.region 0 sp sl)) fun _ _ => True := by
  rw [show CrtIfma.region 0 sp sl = CrtIfma.k1 ++ (.block (CrtIfma.arr52 0 Public.aN oM) ::
    .block (CrtIfma.arr52 0 aT oK1) :: .block (CrtIfma.arr52 0 aXc oX) :: .block (CrtIfma.arr52 0 Public.aY oY) ::
    .block (CrtIfma.arr52 0 Public.aY oFin) :: .block (CrtIfma.k0St 0) :: .block CrtIfma.eZero ::
    CrtIfma.eCopy sp sl) from rfl]
  refine k1_ct (List.cons_ne_nil _ _) ?_
  refine ct_cons (List.cons_ne_nil _ _) (arr52_ct (by decide) (by taint_decide) (by taint_decide))
    (fun _ _ h => arr52_rt (by decide) (by decide) h) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => arr52_rt (by decide) (by decide) h.1) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => arr52_rt (by decide) (by decide) h.1) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => arr52_rt (by decide) (by decide) h.1) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => arr52_rt (by decide) (by decide) h.1) ?_
  refine ct_cons (List.cons_ne_nil _ _) (k0St_ct 0 (by taint_decide)) (fun _ _ h => k0St_rt h) ?_
  refine ct_cons (by simp [CrtIfma.eCopy]) (eZero_ct 0) (fun _ _ h => eZero_rt h) ?_
  exact two_map id (fun _ _ h => ⟨h.1, h.2.1⟩) (eCopy_ct hT)

/-- `q`'s region is constant time. -/
theorem region1_ct {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two (RegPre 1 sp sl)) (seqs (CrtIfma.region 1 sp sl)) fun _ _ => True := by
  rw [show CrtIfma.region 1 sp sl = CrtIfma.k1 ++ (.block (CrtIfma.arr52 1 Public.aN oM) ::
    .block (CrtIfma.arr52 1 aT oK1) :: .block (CrtIfma.arr52 1 aXc oX) :: .block (CrtIfma.arr52 1 Public.aY oY) ::
    .block (CrtIfma.k0St 1) :: .block CrtIfma.eZero :: .block CrtIfma.finOne :: CrtIfma.eCopy sp sl) from rfl]
  refine k1_ct (List.cons_ne_nil _ _) ?_
  refine ct_cons (List.cons_ne_nil _ _) (arr52_ct (by decide) (by taint_decide) (by taint_decide))
    (fun _ _ h => arr52_rt (by decide) (by decide) h) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => arr52_rt (by decide) (by decide) h.1) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => arr52_rt (by decide) (by decide) h.1) ?_
  refine ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => arr52_rt (by decide) (by decide) h.1) ?_
  refine ct_cons (List.cons_ne_nil _ _) (k0St_ct 1 (by taint_decide)) (fun _ _ h => k0St_rt h) ?_
  refine ct_cons (List.cons_ne_nil _ _) (eZero_ct 1) (fun _ _ h => eZero_rt h) ?_
  refine ct_cons (by simp [CrtIfma.eCopy]) finOne_ct (fun _ _ h => finOne_rt h) ?_
  exact eCopy_ct hT

end VG.Proof.Bignum.X86_64
