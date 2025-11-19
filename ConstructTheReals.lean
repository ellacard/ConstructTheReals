-- Get-ChildItem ConstructTheReals -Recurse -Filter *.lean | % { "import " + ($_.FullName -replace '\\','/' -replace '^.*ConstructTheReals/','ConstructTheReals/' -replace '\.lean$','' -replace '/','.') }

import ConstructTheReals.Field
import ConstructTheReals.Function
import ConstructTheReals.Group
import ConstructTheReals.Integer
import ConstructTheReals.Localization
import ConstructTheReals.Logic
import ConstructTheReals.Magma
import ConstructTheReals.MetricSpace
import ConstructTheReals.Monoid
import ConstructTheReals.Natural
import ConstructTheReals.Operation
import ConstructTheReals.Pointed
import ConstructTheReals.Rational
import ConstructTheReals.Real
import ConstructTheReals.Relation
import ConstructTheReals.Ring
import ConstructTheReals.Set
