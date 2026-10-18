module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VPieces
public import VerifiedGarbage.Proof.RsaPss.X86_64.Goods
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecLoops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the frame's shape through `saltBack`

As `VPieces.lean`, for the pieces of `fixedBack` and `autoBack`: the prefix,
the hash calls' arguments, the buffer and its shift, the copies of the
streaming state, and one candidate of the loop (`vcand_step`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sCtr sHD oEm oSt oDig oLh oBuf oW oRsa scr lay)
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Impl.RsaOaep.X86_64 (shift)
open VG.Proof.RsaOaep.X86_64 (encStack fb Lay Rep upd nW inR Good wp_good block_good keep_cs3 lenOf tw Fns
  sizes scr_ok cpV clrV)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Proof.HashFns (StreamingOK)

variable {s : State}

/-! ## The prefix and the hash calls' arguments -/

theorem vmp_step {P : State → (Nat → BitVec 64) → Prop} (hp : VPre s) (hr9 : (s.gpr .r9).toNat = vD s)
    {t : State} (h : VS P s t) : WP isa mPrefix t (VS P s) := by
  obtain ⟨-, -, hD16, hD64, -, -, -⟩ := h.2.2.2.sizes hp
  have e1 : vD s = lenOf (vselH s) := rfl
  rw [e1] at hD16 hD64 hr9
  have hsl' := hp.hsl'
  have hwD := hp.wD
  have hwS := hp.wS
  refine WP.mono (vs_stepW (X := fun _ => True) mPrefix_good (rs := [.rsi, .rcx, .r10, .rax, .r8]) (by decide) h
    fun V W R hA _ _ _ => ?_) fun _ h => h.1
  obtain ⟨-, -, -, -, -, -, w27, -⟩ := hA.w
  exact WP.mono (mPrefix_ok h.2.1 R w27 hA.sel.1 (by omega) hD64
      (fun i hi => by
        rw [h.1.rd, hp.hrd]
        exact ⟨dgR s, List.mem_append_left _ (by simp [vrd]),
          Offset.contains_base _ (by rw [hr9]; omega) (by omega)⟩)
      (fun i hi j hj => VG.Proof.RsaOaep.X86_64.ne_of_disjoint hp.ddS
        (Offset.contains_base _ (by rw [hr9]; omega) (by omega))
        (Offset.contains_base _ (by unfold oMp; omega) (by unfold oMp; omega))))
    fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩

/-- The state's address into `rdi`. -/
theorem vscr_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : VS P s t) :
    WP isa (.block (scr .rdi oSt)) t fun t' => VS P s t' ∧ t'.gpr .rdi = off (stackArg s 4) oSt :=
  vs_stepM (block_good _ rfl rfl) (rs := [.rdi]) (by decide) (by decide) h fun _ _ _ _ _ _ _ =>
    WP.mono (scr_ok h.2.1 (d := .rdi) (by decide) (o := oSt) (by decide)) fun _ ⟨a, b, c⟩ => ⟨b, c, a⟩

/-- The arguments of `update`, with the `len` bytes at `scratch + o`, after
`cnt`. -/
def RU (o len cnt : Nat) (s t : State) : Prop :=
  t.gpr .rdi = off (stackArg s 4) oSt ∧ t.gpr .rsi = BitVec.ofNat 64 cnt ∧ t.gpr .rdx = off (stackArg s 4) o ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .r8 = off (stackArg s 4) oW

/-- The arguments of `finalize`, to `scratch + o`, after `cnt`. -/
def RF (o cnt : Nat) (s t : State) : Prop :=
  t.gpr .rdi = off (stackArg s 4) oSt ∧ t.gpr .rsi = BitVec.ofNat 64 cnt ∧ t.gpr .rdx = off (stackArg s 4) o ∧
    t.gpr .rcx = off (stackArg s 4) oW

theorem vpre_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : VS P s t) :
    WP isa (.block (scr .rdi oSt ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ scr .rdx oMp ++
      ([.mov .rcx (.mem (sp sHD)), .alu .add .rcx (.imm 8)] : List Instr) ++ scr .r8 oW)) t
      fun t' => VS P s t' ∧ RU oMp (vD s + 8) 0 s t' :=
  vs_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx, .r8]) (by decide) (by decide) h
    fun _ _ R hA _ _ _ => WP.mono (updPre_ok h.2.1 R hA.sel.1) fun _ ⟨a, b, c, d, e, f, g⟩ =>
      ⟨f, g, a, b, c, d, e⟩

theorem vsl_fixed (hfx : vfixed s = true) : vsl s = (stackArg s 3).toNat := by
  unfold vsl; rw [ifp hfx]

theorem vfix_step {P : State → (Nat → BitVec 64) → Prop} (hp : VPre s) (hfx : vfixed s = true) {t : State}
    (h : VS P s t) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.mov .rdx (.mem (sp sEb)), .alu .add .rdx (.mem (sp sDb)),
      .alu .sub .rdx (.mem (sp sSlen)), .mov .rcx (.mem (sp sSlen))] : List Instr) ++ scr .r8 oW)) t
      fun t' => VS P s t' ∧ RU (vE s + vDb s - vsl s) (vsl s) (vD s + 8) s t' := by
  obtain ⟨-, -, -, -, -, d6, -⟩ := h.2.2.2.sizes hp
  rw [vsl_fixed hfx] at d6 ⊢
  exact vs_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx, .r8]) (by decide) (by decide) h
    fun _ W R hA h33 h44 _ => by
      obtain ⟨-, -, -, -, -, -, -, -, w29, -⟩ := hA.w
      exact WP.mono (updFix_ok h.2.1 R hA.sel.1 h33 h44 (sl := (stackArg s 3).toNat)
          (by rw [w29, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega))
        fun _ ⟨a, b, c, d, e, f, g⟩ => ⟨f, g, a, b, c, d, e⟩

theorem vfinSl_step {P : State → (Nat → BitVec 64) → Prop} (hfx : vfixed s = true) {t : State}
    (h : VS P s t) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.alu .add .rsi (.mem (sp sSaltLen))] : List Instr) ++ scr .rdx oDig ++
      scr .rcx oW)) t fun t' => VS P s t' ∧ RF oDig (vD s + 8 + vsl s) s t' := by
  rw [vsl_fixed hfx]
  exact vs_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx]) (by decide) (by decide) h
    fun _ W R hA _ _ _ => by
      obtain ⟨-, -, -, -, -, -, -, -, w29, -⟩ := hA.w
      exact WP.mono (finSl_ok h.2.1 R hA.sel.1 (sl := (stackArg s 3).toNat)
          (by rw [w29, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (o := oDig) (by decide))
        fun _ ⟨a, b, c, d, e, f⟩ => ⟨e, f, a, b, c, d⟩

/-! ## The buffer -/

/-- `DB` copied to the buffer, cleared after it. -/
def RB (s t : State) : Prop :=
  t.gpr .rcx = off (stackArg s 4) oBuf ∧ ∀ x, 1024 ≤ x → x < 2048 → t.mem (off (stackArg s 4) (oBuf + x)) = 0

theorem vcopyDb_step (hp : VPre s) {t : State} (h : VS PP s t) :
    WP isa copyDb t fun t' => VS PP s t' ∧ RB s t' := by
  obtain ⟨d1, d2, -⟩ := h.2.2.2.sizes hp
  exact vs_stepW copyDb_good (rs := [.rcx, .rsi, .r10, .rax, .r8]) (by decide) h fun V W R hA h33 h44 _ =>
    WP.mono (copyDb_ok h.2.1 R h33 h44 d1 (by omega)) fun t' ⟨L', k', hcx, R'⟩ => ⟨L', k', ⟨_, R'⟩, hcx,
      fun x h1 h2 => by
        rw [R'.scr _ (by unfold oBuf oRsa; omega), cpV, ifn (by unfold oBuf at *; omega), clrV,
          ifp ⟨by omega, by omega⟩]⟩

theorem vshift_step (hp : VPre s) {t : State} (h : VS PP s t) (hb : RB s t) :
    WP isa shift t (VS PP s) := by
  obtain ⟨-, -, -, -, -, -, d7⟩ := h.2.2.2.sizes hp
  refine WP.mono (vs_step (X := fun _ => True) VG.Proof.RsaOaep.X86_64.shift_good
    (rs := [.rax, .rcx, .rsi, .r11, .r9, .r8, .rdi, .rdx, .r10]) (by decide) h fun V W R _ _ _ hP => ?_)
    fun _ h => h.1
  obtain ⟨pos, hpos, hlt⟩ := hP
  exact WP.mono (VG.Proof.RsaOaep.X86_64.shift_ok h.2.1 R hb.1 hpos (by omega) fun x h1 h2 => by
      rw [← R.scr _ (by unfold oBuf oRsa; omega)]; exact hb.2 x h1 h2)
    fun t' ⟨L', k', V', W', R', hW, _⟩ => ⟨L', k', ⟨V', W', R', fun k hk => hW k (vkey_lt hk)
      (vkey_ne hk (by omega)) (vkey_ne hk (by omega)) (vkey_ne hk (by omega)),
      pos, (hW 32 (by decide) (by decide) (by decide) (by decide)).trans hpos, hlt⟩, trivial⟩

/-- The 256 bytes at `scratch + a` copied to `scratch + b`. -/
theorem vcopyQ_step {P : State → (Nat → BitVec 64) → Prop} {a b : Nat} (ha : a + 256 ≤ oRsa)
    (hb : b + 256 ≤ oRsa) (hab : a + 256 ≤ b ∨ b + 256 ≤ a) (ha31 : a < 2 ^ 31) (hb31 : b < 2 ^ 31) {t : State}
    (h : VS P s t) : WP isa (copyQ a b) t (VS P s) :=
  WP.mono (vs_stepW (X := fun _ => True) (copyQ_good a b) (rs := [.rsi, .rdi, .rax, .r8]) (by decide) h
    fun _ _ R _ _ _ _ => WP.mono (copyQ_ok h.2.1 R ha hb hab ha31 hb31) fun _ ⟨L', k', R'⟩ =>
      ⟨L', k', ⟨_, R'⟩, trivial⟩) fun _ h => h.1

/-! ## The candidates -/

/-- The candidate `c`, in its slot. -/
def PK (c : Nat) (_ : State) (W : Nat → BitVec 64) : Prop := W 19 = BitVec.ofNat 64 c

theorem vctr0_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : VS P s t) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax]) t (VS (PK 0) s) :=
  WP.mono (vs_step (X := fun _ => True) (block_good _ rfl rfl) (rs := [.rax]) (by decide) h fun _ _ R _ _ _ _ =>
    WP.mono (ctr0_ok h.2.1 R) fun _ ⟨L', k', R'⟩ =>
      ⟨L', k', ⟨_, _, R', fun k hk => upd_key (by omega) _ hk, by simp [PK, upd]⟩, trivial⟩) fun _ h => h.1

theorem vfinArgs_step {c : Nat} {t : State} (h : VS (PK c) s t) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.alu .add .rsi (.mem (sp sCtr))] : List Instr) ++ scr .rdx oLh ++
      scr .rcx oW)) t fun t' => VS (PK c) s t' ∧ RF oLh (vD s + 8 + c) s t' :=
  vs_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx]) (by decide) (by decide) h
    fun _ _ R hA _ _ hP => WP.mono (finCandArgs_ok h.2.1 R hA.sel.1 hP) fun _ ⟨a, b, c, d, e, f⟩ =>
      ⟨e, f, a, b, c, d⟩

theorem vselC_step {c : Nat} (hc : c < 2 ^ 64) {t : State} (h : VS (PK c) s t) : WP isa selCand t (VS (PK c) s) :=
  WP.mono (vs_stepW (X := fun _ => True) selCand_good (rs := [.rax, .r11, .rcx, .rdi, .r8, .rdx]) (by decide) h
    fun _ W R _ _ _ hP => WP.mono (selCand_ok h.2.1 R (l := (W 5).toNat) hP
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) hc (W 5).isLt) fun _ ⟨L', k', R'⟩ =>
      ⟨L', k', ⟨_, R'⟩, trivial⟩) fun _ h => h.1

theorem vupdArgs_step {c : Nat} {t : State} (h : VS (PK c) s t) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.alu .add .rsi (.mem (sp sCtr))] : List Instr) ++ scr .rdx oBuf ++
      ([.alu .add .rdx (.mem (sp sCtr)), .mov32 .rcx (.imm 1)] : List Instr) ++ scr .r8 oW)) t
      fun t' => VS (PK c) s t' ∧ RU (oBuf + c) 1 (vD s + 8 + c) s t' :=
  vs_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx, .r8]) (by decide) (by decide) h
    fun _ _ R hA _ _ hP => WP.mono (updCandArgs_ok h.2.1 R hA.sel.1 hP) fun _ ⟨a, b, c, d, e, f, g⟩ =>
      ⟨f, g, a, b, c, d, e⟩

theorem vnext_step (hp : VPre s) {c : Nat} (hc : c < vDb s) {t : State} (h : VS (PK c) s t) :
    WP isa (.block nextCand) t fun t' => VS (PK (c + 1)) s t' ∧ t'.zf = some (decide (c + 1 = vDb s)) := by
  obtain ⟨-, -, -, -, -, -, d7⟩ := h.2.2.2.sizes hp
  exact vs_step (block_good _ rfl rfl) (rs := [.rax]) (by decide) h fun _ _ R _ _ h44 hP =>
    WP.mono (nextCand_ok h.2.1 R hP h44 (by omega) (by omega)) fun _ ⟨L', k', hz, R'⟩ =>
      ⟨L', k', ⟨_, _, R', fun k hk => upd_key (by omega) _ hk, by simp [PK, upd]⟩, hz⟩

variable {TH : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)

include hTH in
/-- One candidate `c < dbLen`. -/
theorem vcand_step (hp : VPre s) (fH : VFns s TH 10) {c : Nat} (hc : c < vDb s) {t : State}
    (h : VS (PK c) s t) :
    WP isa cand t fun t' => t'.zf = some (decide (c + 1 = vDb s)) ∧ VS (PK (c + 1)) s t' := by
  obtain ⟨-, -, -, -, -, -, d7⟩ := h.2.2.2.sizes hp
  unfold cand seqs seqs seqs seqs seqs seqs
  refine WP.seq (WP.mono (vcopyQ_step (a := oSt2) (b := oSt) (by decide) (by decide) (by decide) (by decide)
    (by decide) h) fun t1 h1 => ?_)
  unfold finCand
  refine WP.seq (WP.seq (WP.mono (vfinArgs_step h1) fun t2 ⟨h2, a, b, d, e⟩ => ?_))
  refine WP.mono (vfin_step hTH (j := 45) (.inl ⟨rfl, rfl⟩) fH h2 (o := oLh) (.inr (by decide)) a d e)
    fun t3 h3 => ?_
  refine WP.seq (WP.mono (vselC_step (by omega) h3) fun t4 h4 => ?_)
  refine WP.seq (WP.mono (vcopyQ_step (a := oSt2) (b := oSt) (by decide) (by decide) (by decide) (by decide)
    (by decide) h4) fun t5 h5 => ?_)
  unfold updCand
  refine WP.seq (WP.seq (WP.mono (vupdArgs_step h5) fun t6 ⟨h6, a, b, d, e, f⟩ => ?_))
  refine WP.mono (vupd_step hTH (j := 45) (.inl ⟨rfl, rfl⟩) fH h6 (a := oBuf + c) (len := 1)
    (by unfold oBuf oRsa; omega) (.inl (by unfold oBuf oSt; omega)) (.inl (by unfold oBuf oW; omega)) a d e f)
    fun t7 h7 => ?_
  refine WP.seq (WP.mono (vcopyQ_step (a := oSt) (b := oSt2) (by decide) (by decide) (by decide) (by decide)
    (by decide) h7) fun t8 h8 => ?_)
  exact WP.mono (vnext_step hp hc h8) fun _ ⟨a, b⟩ => ⟨b, a⟩

end VG.Proof.RsaPss.X86_64
