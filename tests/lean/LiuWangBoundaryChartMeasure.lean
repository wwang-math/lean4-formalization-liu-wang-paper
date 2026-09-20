import LiuWang.LiuWang2025SemilinearWaveBoundaryChartMeasure

open MeasureTheory
open LiuWang2025SemilinearWaveBoundaryChartMeasure

#check CompactBoundaryChartDensity.exists_nonnegative_upper_bound
#check CompactBoundaryChartDensity.surfaceMeasure_le_smul_restrict
#check CompactBoundaryChartDensity.integral_surfaceMeasure_le
#check CompactBoundaryChartDensity.integral_sqNorm_surfaceMeasure_le
#check CompactBoundaryChartDensity.integral_sqNorm_surfaceMeasure_le_of_coordinate_bound
#check CompactBoundaryChartDensity.certificate

example
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) :
    chart.Certificate referenceMeasure :=
  chart.certificate referenceMeasure

#print axioms CompactBoundaryChartDensity.exists_nonnegative_upper_bound
#print axioms CompactBoundaryChartDensity.surfaceMeasure_le_smul_restrict
#print axioms CompactBoundaryChartDensity.integral_sqNorm_surfaceMeasure_le
#print axioms CompactBoundaryChartDensity.integral_sqNorm_surfaceMeasure_le_of_coordinate_bound
#print axioms CompactBoundaryChartDensity.certificate
