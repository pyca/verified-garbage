import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase

/-!
# RSAES-OAEP on AArch64: MGF1 in constant time

`mgfXor` from two runs in the same frame and working space with the same
arguments in MGF1's slots: each round from two runs at the same counter
(`MX`) by its blocks and calls (`round_tr`), the counter's bytes stored
through a pointer the block loads, so it is split there; the rounds, whose
number is fixed by the lengths, by `count_ct` (`mgfXor_tr`).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs round xorOut xorHead xorBody nextCtr initArgs updSrcArgs updCtrArgs finArgs
  mgfXor)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

/-- MGF1's slots, and the counter `c` and `done` in theirs. -/
def MX (S : Addr) (src srcLen dst dstLen D c : Nat) (W : Nat → BitVec 64) (_ : State) : Prop :=
  MArgs W S src srcLen dst dstLen ∧ W 17 = BitVec.ofNat 64 c ∧ W 18 = BitVec.ofNat 64 (c * D)

theorem lt_ceil {a D j : Nat} (hD : 0 < D) : j < (a + D - 1) / D ↔ j * D < a := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]; omega

theorem updCtrArgs_eq : updCtrArgs lay = Mgf1.scr lay .x2 lay.oCtr ++ (([.ldrSp .x10 lay.sCtr, .strb .x10 .x2 3,
    .lsr .x .x10 .x10 8, .strb .x10 .x2 2, .lsr .x .x10 .x10 8, .strb .x10 .x2 1, .lsr .x .x10 .x10 8,
    .strb .x10 .x2 0] : List Instr) ++ Mgf1.scr lay .x0 lay.oSt ++ ([.ldrSp .x1 lay.sSrcLen, .movz .x .x3 4 0] :
    List Instr) ++ Mgf1.scr lay .x4 lay.oW) := by
  simp only [updCtrArgs, List.append_assoc]

variable {G : Hash} (hG : StreamOK G.stream)

include hG in
theorem round_tr {F S : Addr} {src srcLen dst dstLen c : Nat} (hf : MFit src srcLen dst dstLen)
    (hc : c * G.D < dstLen) :
    RelCT isa (LR F S (MX S src srcLen dst dstLen G.D c)) (round lay G)
      (LR F S fun W t => MX S src srcLen dst dstLen G.D (c + 1) W t ∧
        (t.gpr .x12 != 0) = decide ((c + 1) * G.D < dstLen)) := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have eD : G.stream.D = G.D := rfl
  rw [eD] at hzDF hzD
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 3520 := rfl
  have c5 : oRsa = 8192 := rfl
  have hfs := hf.fs
  have hfd := hf.fd
  have hdb := hf.dstB
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hzD
  unfold round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine (lr_wp (X' := fun W t => MX S src srcLen dst dstLen G.D c W t ∧ t.gpr .x0 = off S oSt)
    (lr_taint [] (by taint_decide) nopin) fun t V W L R hx => WP.mono (initArgs_ok L []) fun u ⟨Su, hm, x0⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx, x0⟩).seq ?_
  refine (lr_wp (X' := MX S src srcLen dst dstLen G.D c) (lr_init hG fun _ _ h => h.2)
    fun t V W L R ⟨hx, x0⟩ => WP.mono (init_ok hG L R x0 []) fun u ⟨Lu, _, Ru, _⟩ => ⟨_, W, Lu, Ru, hx⟩).seq ?_
  -- `update` with `src`.
  refine (lr_wp (X' := fun W t => MX S src srcLen dst dstLen G.D c W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ t.gpr .x2 = off S src ∧ t.gpr .x3 = BitVec.ofNat 64 srcLen ∧
      t.gpr .x4 = off S oW) (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (updSrc_ok L R hx.1 []) fun u ⟨Su, hm, x0, x1, x2, x3, x4⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx, x0, x1, x2, x3, x4⟩).seq ?_
  refine (lr_wp (X' := MX S src srcLen dst dstLen G.D c) (lr_upd hG (BitVec.ofNat 64 0) (a := src) (len := srcLen)
      (by omega) (by omega) (by omega) fun _ _ h => h.2)
    fun t V W L R ⟨hx, x0, _, x2, x3, x4⟩ => WP.mono (upd_ok hG L R (by omega) (by omega) (by omega) x0 x2 x3 x4 [])
      fun u ⟨Lu, _, Ru, _⟩ => ⟨_, W, Lu, Ru, hx⟩).seq ?_
  -- The counter, and `update` with it.
  refine (lr_wp (X' := fun W t => MX S src srcLen dst dstLen G.D c W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 srcLen ∧ t.gpr .x2 = off S oCtr ∧ t.gpr .x3 = BitVec.ofNat 64 4 ∧
      t.gpr .x4 = off S oW) (by
        rw [updCtrArgs_eq]
        exact RelCT.block_append (lr_seq_tr [.x2] (fun _ => off S oCtr) (by taint_decide) (by taint_decide)
          fun t V W L R _ => WP.mono (scr_pin L .x2 (o := oCtr) (by decide)) fun u ⟨hs, x2⟩ =>
            ⟨hs, fun r hr => by rw [List.mem_singleton.mp hr]; exact x2⟩))
    fun t V W L R hx => WP.mono (updCtr_ok L R hx.1.hsl hx.2.1 (by omega) [])
      fun u ⟨Lu, _, Ru, x0, x1, x2, x3, x4⟩ => ⟨_, W, Lu, Ru, hx, x0, x1, x2, x3, x4⟩).seq ?_
  refine (lr_wp (X' := MX S src srcLen dst dstLen G.D c) (lr_upd hG (BitVec.ofNat 64 srcLen) (a := oCtr) (len := 4)
      (by omega) (by omega) (by omega) fun _ _ h => h.2)
    fun t V W L R ⟨hx, x0, _, x2, x3, x4⟩ => WP.mono (upd_ok hG L R (a := oCtr) (len := 4) (by omega) (by omega)
      (by omega) x0 x2 x3 x4 []) fun u ⟨Lu, _, Ru, _⟩ => ⟨_, W, Lu, Ru, hx⟩).seq ?_
  -- `finalize`.
  refine (lr_wp (X' := fun W t => MX S src srcLen dst dstLen G.D c W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 (srcLen + 4) ∧ t.gpr .x2 = off S oDig ∧ t.gpr .x3 = off S oW)
    (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (finA_ok L R hx.1.hsl []) fun u ⟨Su, hm, x0, x1, x2, x3⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx, x0, x1, x2, x3⟩).seq ?_
  refine (lr_wp (X' := MX S src srcLen dst dstLen G.D c) (lr_fin hG (BitVec.ofNat 64 (srcLen + 4)) (o := oDig)
      (.inr (by decide)) fun _ _ h => h.2)
    fun t V W L R ⟨hx, x0, _, x2, x3⟩ => WP.mono (fin_ok hG L R (o := oDig) (.inr (by decide)) x0 x2 x3 [])
      fun u ⟨Lu, _, Ru, _⟩ => ⟨_, W, Lu, Ru, hx⟩).seq ?_
  -- Into `dst`.
  refine (lr_wp (X' := MX S src srcLen dst dstLen G.D c) (lr_seq_tr [.x11, .x12, .x14]
      (fun r => if r = .x11 then off S oDig else if r = .x12 then off S (dst + c * G.D)
        else BitVec.ofNat 64 (min G.D (dstLen - c * G.D)))
      (check_of_zImm (τ := Taint.ofRegs []) (c := .block (xorHead lay G)) (c' := .block (xorHead lay gH)) rfl
        (by taint_decide)) (by taint_decide)
      fun t V W L R hx => WP.mono (xorHead_ok L R (G := G) (by omega) (by omega) hx.1.hdst hx.1.hdl hx.2.2 hc [])
        fun u ⟨Su, _, x11, x12, x14⟩ => ⟨Su.sp, by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl) <;> simp [x11, x12, x14]⟩)
    fun t V W L R hx => WP.mono (xorOut_ok L R hfd hzD (by omega) hx.1.hdst hx.1.hdl hx.2.2 hc [])
      fun u ⟨Lu, _, Ru⟩ => ⟨_, W, Lu, Ru, hx⟩).seq ?_
  -- The next counter.
  refine lr_wp (lr_taint [] (check_of_zImm (τ := Taint.ofRegs []) (c := .block (nextCtr lay G))
      (c' := .block (nextCtr lay gH)) rfl (by taint_decide)) nopin)
    fun t V W L R hx => WP.mono (nextCtr_ok L R (G := G) hx.2.1 hx.2.2 hx.1.hdl (by omega) (by omega) (by omega) [])
      fun u ⟨Lu, _, x12, Ru⟩ => ⟨_, _, Lu, Ru, ⟨hx.1.of_eq fun k h1 h2 => by
        simp only [upd]; rw [ifn (by omega), ifn (by omega)], by simp [upd], by simp [upd, Nat.succ_mul]⟩,
        by rw [x12, Nat.succ_mul]⟩

include hG in
theorem mgfXor_tr {F S : Addr} {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen)
    {X : (Nat → BitVec 64) → State → Prop} (hX : ∀ W t, X W t → MArgs W S src srcLen dst dstLen) :
    RelCT isa (LR F S X) (mgfXor lay G) fun _ _ => True := by
  obtain ⟨-, -, -, -, hzD⟩ := sizes hG
  replace hzD : 0 < G.D := hzD
  have hN : 0 < (dstLen + G.D - 1) / G.D := (lt_ceil hzD).mpr (by have := hf.pos; omega)
  refine (lr_wp (X' := MX S src srcLen dst dstLen G.D 0) (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (mgfHead_ok L R [] dst dstLen G.D) fun u I => ?_).seq
    ((count_ct hN (fun c => LR F S (MX S src srcLen dst dstLen G.D c)) fun c hc =>
      (round_tr hG hf ((lt_ceil hzD).mp hc)).mono (fun _ _ h => h)
        fun a b ⟨⟨Va, Wa, La, Ra, xa, ca⟩, ⟨Vb, Wb, Lb, Rb, xb, cb⟩⟩ =>
          ⟨⟨⟨Va, Wa, La, Ra, xa⟩, ⟨Vb, Wb, Lb, Rb, xb⟩⟩,
            by rw [ca]; exact decide_eq_decide.mpr (by rw [← lt_ceil hzD]; omega),
            by rw [cb]; exact decide_eq_decide.mpr (by rw [← lt_ceil hzD]; omega)⟩).mono
      (fun _ _ h => h) fun _ _ _ => trivial)
  obtain ⟨V', W', R', h17, h18, hW, -⟩ := I.rep
  exact ⟨V', W', I.L, R', (hX W t hx).of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega) (by omega)
    (by omega), h17, by rw [h18, Nat.zero_mul]⟩

end VG.Proof.RsaOaep.AArch64
