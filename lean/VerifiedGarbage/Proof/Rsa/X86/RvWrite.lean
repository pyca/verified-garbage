module
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Rsa.X86.RvViews
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Updating the arrays and scalar words tracked by a recovery stage -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.write_w {o x : Nat} {ds : List Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B g.w [o] ds s.mem t.mem) (ho : o < nArr) (hd : ∀ d ∈ ds, SlotOk d)
    (r : Keeps opRegs s t) (e : num t.mem g.B g.w o = x)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j)
    (hls : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) :
    KS g s0 (upd A o x) (o :: live) AW liveW V ls t :=
  h.core k (by simpa using h.ws.arr_fit ho) hd r
    (h.arrs.upd1 k (fun d hm => (hd d hm).2.1) (fun j hj => h.ws.fit64 (h.live_lt j hj)) e)
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.live_lt j))
    (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj) hd) h.liveW_lt
    (h.sl_keep k hls) h.ls_ok

theorem KS.write_W {o x : Nat} {ds : List Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B g.W [o] ds s.mem t.mem) (ho : o < 22) (hd : ∀ d ∈ ds, SlotOk d)
    (r : Keeps opRegs s t) (e : num t.mem g.B g.W o = x)
    (hl : ∀ j ∈ live, j / 2 ≠ o)
    (hls : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) :
    KS g s0 A live (upd AW o x) (o :: liveW) V ls t :=
  h.core k (by simpa using h.wsW.arr_fit ho) hd r
    (h.arrs_W k (fun j hj i hi => by simp at hi; subst hi; exact hl j hj) hd) h.live_lt
    (h.arrsW.upd1 k (fun d hm => (hd d hm).2.1) (fun j hj => h.wsW.fit64 (h.liveW_lt j hj)) e)
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ ho) (h.liveW_lt j))
    (h.sl_keep k hls) h.ls_ok

theorem KS.slot1 {d x v : Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B v [] [d] s.mem t.mem) (hd : SlotOk d) (r : Keeps opRegs s t)
    (e : slot t.mem g.B d = x) : KS g s0 A live AW liveW (upd V d x) (d :: ls) t := by
  have kw : Keep g.B g.w [] [d] s.mem t.mem := k
  refine h.core kw (by simp) (by simpa using hd) r
    (h.arrs_w kw (by simp) (by simpa using hd)) h.live_lt
    (h.arrsW_w kw (by simp) (by simpa using hd)) h.liveW_lt ?_ ?_
  · intro d' hd'
    by_cases eq : d' = d
    · subst eq; rw [upd_self]; exact e
    · have old := (List.mem_cons.mp hd').resolve_left eq
      have info := h.ls_ok d' old
      rw [upd_ne _ _ eq, kw.slot info.2.1 (fun z hz => by
        simp only [List.mem_singleton] at hz
        subst hz
        have := info.2.2; have := hd.2.2; omega), h.sl d' old]
  · intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | old
    · exact hd
    · exact h.ls_ok d' old

end
end VG.Proof.Rsa.X86.Recover
