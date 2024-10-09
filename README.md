# topofix
Fix and add topo data to OSM in Norway
### Usage

<code>python topofix.py \<municipality\> [-overlap] [-mergeprop] [-merge] [-simplify] [-water] [-river] [-help]</code>


### Options ###

For all arguments below (or with no arguments), topo relations will be reordered if needed. Outer members will be put at the top and inner members below. Inner members will be ordered according to the size of the inner area. Affected relations will get a **REORDER=*** tag. A warning will be given if more than one outer member area exist + an **OUTER=*** tag on the relation. A file of the format _topofix_4207_Flekkefjord.osm_ will be produced. Please note that this file will be overwritten by each run below.

The following arguments should be used in the described order, preferably one argument only in each run.

1. <code>-overlap</code>

   This function will merge overlapping ways (ways with same position). These cases may be caused by insufficient merging between for example water features and wood features when the import was done. Merged ways will get a **OVERLAP=*** tag. Merged ways which are horizontal or vertical parts of a wood grid will also get a **GRID=*** tag.

   Fix any validation errors and warnings in JOSM and upload to OSM.

2. <code>-mergeprep</code>

   This function will propose relations to be merged in the next <code>-merge</code> step. This way, features will no longer be split along municipality boundaries. Ways which are connecting the relations to be merged will get a **FIXME=*** tag.
   * **FIXME=Merge** will mark ways which will be removed when relations are merged.
   * **FIXME=Merge incomplete** will mark cases where you need to first download members of one of the merging relations. Search for <code>FIXME=parent("Merge incomplete") (parent(incomplete) or parent(parent(incomplete)))</code> in JOSM, then select the _Download members_ function in the popup menu. After downloading, please modify the tag to **FIXME=Merge**.
   * **FIXME=Join** will mark the same as **FIXME=Merge**, but where two ways overlapping ways were merged.

   Modify the proposed **FIXME=*** tags and add new ways with **FIXME=Split** tags as needed in order to get complete relations without cut-offs at municipality borders. Take care to ensure that the large wood grids are not combined due to **FIXME=Merge** (one or more **FIXME=Split** might be needed to contain the grid). Note that a way with **FIXME=Split** must end onto members of the same relation at each end of the way, and that ways containing any end nodes must be split at that node. Check that there are no **FIXME=Merge/Join** between lakes which are intendend to stay as separate objects. Also, do not merge features across municipality boundaries if one of the municipalities have not been imported yet.

   Please store the modified file with a __merge.osm_ ending, for example _topofix_4207_Flekkefjord_merge.osm_. It will be loaded by the <code>-merge</code> function below, and it will not be overwritten.

3. <code>-merge</code>

   This function will first split, then merge, relations according to **FIXME=*** instructions given as described above. Please modify the __merge.osm_ file if any error messages are displayed. Splitted relations will be marked with a **SPLIT=*** tag and merged relations will be marked with a **MERGED=*** tag.

   Ways with a **FIXME=Split** tag which failed to split a relation will be marked with a **NO_SPLIT=*** tag. You may need to re-run this function a few times after modifying the __merge.osm_ file to get the desired result.

   Fix any validation errors and warnings in JOSM and upload to OSM.

5. <code>-simplify</code>

   This function will concatenate member ways in a relation to form a full connected polygon is possible. Relations which consequently only have one member will be converted into a way (tags will be relocated to the member way and the relation will be deleted). Run this function before the <code>-water</code> function below, but do not run it if the relations in question will be needed later, for example if an import is incomplete.

   Fix any validation errors and warnings in JOSM and upload to OSM.

6. <code>-water</code>

   This function will carry out a number of actions on lakes:
   * Identify islands and tag them with **place=island/islet**.
   * Load reference id and elevations from the NVE lake database, including special tagging for reservoirs (**water=reservoir** + **ele:min=***).
   * Load elevations for non-NVE lakes from the DTM height model of Kartverket.
   * Load names of lakes and islands from the SSR database and propose tagging.

   Process for manual modifcations to proposed names in the produced file:
   * Search for <code>UPDATE_</code> to get names which may have been updated in SSR since last import into OSM. Use the To-do plugin to walk through each case and edit the existing name in OSM if apropriate.
   * Search for <code>FIXME:consider</code> to get extra names which may be relevant for a lake or island. Use the To-do plugin to walk through each case and modify the existing name, add **alt_name=*** (based on the generated **ALT_NAME=***) or add a node with for example **natural=bay** if the name is relevant for part of a lake only. Each extra name is included as a node which may be used or deleted, as apropriate.
   * Repeat this process for <code>FIXME:verify</code> to check if the assigned name is correct, and to decide what to do with extra names for a lake or island. Some of these names may be duplicates (to be deleted), or alternative names or group names (to be added as **alt_name=***).
   * Repeat this process for <code>FIXME:choose</code> to decide which of two or more names should be used for a lake or island.
   * Search for <code>new waterway=waterfall and new waterway=rapids</code> to check that the proposed position is correct.
   * Search for <code>FIXME:insert</code> to get names which were not matched with any feature. 

   Fix any validation errors and warnings in JOSM and upload to OSM.

6. <code>-river</code>

   This function will carry out a number of actions on rivers and streams:
   * Load names from SSR database and propose tagging.
   * Match rivers/streams with NVE Elvenett river network model, turn direction of way if needed, and recombine river/stream segments into longer ways.
   * Add **waterway** centerlines to **natural=water** + **water=river** relations, including connecting segments for streams across riverbanks.

   There are four alternative arguments for river centerlines:
   * <code>-river</code> - Will add missing centerlines.
   * <code>-extrariver</code> - Will add mising centerlines plus connecting stream segments.
   * <code>-allriver</code> - Will add all NVE centerlines (existing centerlines in OSM must be replaced) and connecting stream segments.
   * <code>-nameriver</code> - Only add names to rivers (no other modifications). 

   Process for manual modifications:
   * Search for <code>FIXME:swap</code> to swap proposed waterway centerlines with any existing centerlines. Use the To-do plugin. You may need to split and cocatenate segments in this step.
   * Search for <code>FIXME:connect</code> to connect new short waterway segments at the riverbank. Use the To-do plugin.
   * Search for <code>FIXME:split</code> to split waterways at the point where they change name, usually at a waterway intersection. Use the To-do plugin. For each case, search for nearby <code>FIXME:insert</code> nodes containing the names. Combine segments with the same name to get long connected ways.
   * Search for <code>FIXME:insert</code> to get remaining river/stream/dam names which did not match. You may in some cases need to map the way needed. Use the To-do plugin.
   * Search for <code>ELVIS waterway=river -name=*</code> to check if existing names should be extended to any river segments.

   Use the topo background map at various zoom levels to get information about how a given river/stream name is extending.

   Fix any validation errors and warnings in JOSM and upload to OSM.


### References ###

* [n50osm](https://github.com/NKAmapper/n50osm) på GitHub
* [ssr2osm](https://github.com/NKAmapper/ssr2osm) på GitHub
* [NVE Lake database](https://www.nve.no/kart/kartdata/vassdragsdata/innsjodatabase/)
* [NVE River network (ELVIS)](https://www.nve.no/kart/kartdata/vassdragsdata/elvenettverk-elvis/)
* [Kartverket place names (SSR)](https://wiki.openstreetmap.org/wiki/No:Import_av_stedsnavn_fra_SSR2)
* [Kartverket DTM](https://www.kartverket.no/api-og-data/terrengdata)

