-- Get-ChildItem ConstructTheReals -Recurse -Filter *.lean | % { "import " + ($_.FullName -replace '\\','/' -replace '^.*ConstructTheReals/','ConstructTheReals/' -replace '\.lean$','' -replace '/','.') }

import ConstructTheReals.Constructions.Integer
import ConstructTheReals.Constructions.Natural
import ConstructTheReals.Constructions.Rational
import ConstructTheReals.Constructions.Real
import ConstructTheReals.GroupTheory.Group
import ConstructTheReals.GroupTheory.Magma
import ConstructTheReals.GroupTheory.Monoid
import ConstructTheReals.GroupTheory.Pointed
import ConstructTheReals.RingTheory.Field
import ConstructTheReals.RingTheory.Localization
import ConstructTheReals.RingTheory.Ring
import ConstructTheReals.SetTheory.Function
import ConstructTheReals.SetTheory.Logic
import ConstructTheReals.SetTheory.Operation
import ConstructTheReals.SetTheory.Relation
import ConstructTheReals.SetTheory.Subset
import ConstructTheReals.Topology.MetricSpace
