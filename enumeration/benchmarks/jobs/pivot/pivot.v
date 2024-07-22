From PolyhedraHirschRank1 Require Import rank_1_update_pivot.
From __DATA__ Require Import A b bases pred_r1 idx_r1 x_I_r1 inv_r1 order_r1 det_r1.

Eval vm_compute in R1.vertex_certif A b bases
  pred_r1 idx_r1 x_I_r1 inv_r1 det_r1 order_r1.