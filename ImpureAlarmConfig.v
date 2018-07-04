Require Import Vpl.Impure.
Require Vpl.ImpureConfig.

Module CoreAlarmed := AlarmImpureMonad Vpl.ImpureConfig.Core.
Export CoreAlarmed.

Ltac bind_imp_destruct H id1 id2 :=
  apply CoreAlarmed.Base.mayReturn_bind in H; destruct H as [id1 [id2 H]].