-- Get-ChildItem ConstructTheReals -Recurse -Filter *.lean | % { "import " + ($_.FullName -replace '\\','/' -replace '^.*ConstructTheReals/','ConstructTheReals/' -replace '\.lean$','' -replace '/','.') }

import ConstructTheReals.General.Real
