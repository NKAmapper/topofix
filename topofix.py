#!/usr/bin/env python3
# -*- coding: utf8


import urllib.request, urllib.parse, urllib.error
import json
import sys
import time
import copy
import math
import unicodedata
import os.path
from xml.etree import ElementTree as ET


version = "1.0.1"

header = {"User-Agent": "nkamapper/n50osm (github)"}

overpass_api = "https://overpass-api.de/api/interpreter"  # Overpass endpoint

import_folder = "~/Jottacloud/osm/stedsnavn/"  # Folder containing import highway files (current working folder tried first)

min_ele_size = 2000  	 	# Minimum square meters for fetching elevation
min_lake_size = 1000000		# Minimum square meters for water=lake tag
island_size = 100000  	 	# Minimum square meters for place=island vs place=islet
max_node_match = 1000000 	# Maximum number of matches between nodes (used by Hausdorff and swap_nodes)
grid_limit = 0.00001		# Maximum degrees deviation from 0.5 degree grids  - old: 0.000005

disregard_sources = ["Kartverket", "Landsat", "Bing", "Orthophoto", "NiB"]  # Do not merge source-tag containing these words

turn_stream = True 			# Turn direction of streams according to NVE direction
combine_streams = True 		# Combine streams with same ElvId in Elvis into longer ways
add_centerlines = True 		# Add centerlines to riverbanks

nve_output = False 			# Output NVE lakes and streams (Elvis) in separate file
debug = False



# Output message to console

def message (text):

	sys.stderr.write(text)
	sys.stderr.flush()



# Format time

def timeformat (sec):

	if sec > 3600:
		return "%i:%02i:%02i hours" % (sec / 3600, (sec % 3600) / 60, sec % 60)
	elif sec > 60:
		return "%i:%02i minutes" % (sec / 60, sec % 60)
	else:
		return "%i seconds" % sec



# Compute approximation of distance between two coordinates, (lon,lat), in meters
# Works for short distances

def distance (point1, point2):

	lon1, lat1, lon2, lat2 = map(math.radians, [point1[0], point1[1], point2[0], point2[1]])
	x = (lon2 - lon1) * math.cos( 0.5*(lat2+lat1) )
	y = lat2 - lat1
	return 6371000.0 * math.sqrt( x*x + y*y )  # Metres



# Compute closest distance from point p3 to line segment [s1, s2].
# Works for short distances.

def line_distance(s1, s2, p3, get_point=False):

	x1, y1, x2, y2, x3, y3 = map(math.radians, [s1[0], s1[1], s2[0], s2[1], p3[0], p3[1]])

	# Simplified reprojection of latitude
	x1 = x1 * math.cos( y1 )
	x2 = x2 * math.cos( y2 )
	x3 = x3 * math.cos( y3 )

	A = x3 - x1
	B = y3 - y1
	dx = x2 - x1
	dy = y2 - y1

	dot = (x3 - x1)*dx + (y3 - y1)*dy
	len_sq = dx*dx + dy*dy

	if len_sq != 0:  # in case of zero length line
		param = dot / len_sq
	else:
		param = -1

	if param < 0:
		x4 = x1
		y4 = y1
	elif param > 1:
		x4 = x2
		y4 = y2
	else:
		x4 = x1 + param * dx
		y4 = y1 + param * dy

	# Also compute distance from p to segment

	x = x4 - x3
	y = y4 - y3
	distance = 6371000 * math.sqrt( x*x + y*y )  # In meters

	if get_point:
		# Project back to longitude/latitude

		x4 = x4 / math.cos(y4)

		lon = math.degrees(x4)
		lat = math.degrees(y4)

		return (distance, (lon, lat))
	else:
		return distance



# Calculate shortest distance from node p to line.

def shortest_distance(p, line):

	d_min = 999999.9  # Dummy
	position = None
	for i in range(len(line) - 1):
		d = line_distance(line[i], line[i+1], p)
		if d < d_min:
			d_min = d
			position = i

	return (d_min, position)



# Calculate length of line

def line_length(line):

	d = 0
	for i in range(len(line) - 1):
		d += distance(line[i], line[i+1])

	return d



# Test if line segments s1 and s2 are crossing.
# Segments have two nodes [(start.x, start.y), (end.x, end.y)].
# Source: https://en.wikipedia.org/wiki/Line–line_intersection#Given_two_points_on_each_line_segment

def crossing_lines (s1, s2):

	d1x = s1[1][0] - s1[0][0]  # end1.x - start1.x
	d1y = s1[1][1] - s1[0][1]  # end1.y - start1.y
	d2x = s2[1][0] - s2[0][0]  # end2.x - start2.x
	d2y = s2[1][1] - s2[0][1]  # end2.y - start2.y

	D = d1x * d2y - d1y * d2x

	if abs(D) < 0.0000000001:  # s1 and s2 are parallel
		return False

	A = s1[0][1] - s2[0][1]  # start1.y - start2.y
	B = s1[0][0] - s2[0][0]  # start1.x - start2.x

	r1 = (A * d2x - B * d2y) / D
	r2 = (A * d1x - B * d1y) / D

	if r1 < 0 or r1 > 1 or r2 < 0 or r2 > 1:
		return False
	'''
	# Compute intersection point

	x = s1[0][0] + r1 * d1x
	y = s1[0][1] + r1 * d1y
	intersection = (x, y)
	return (intersection)
	'''
	return True



# Calculate coordinate area of polygon in square meters
# Simple conversion to planar projection, works for small areas
# < 0: Clockwise
# > 0: Counter-clockwise
# = 0: Polygon not closed

def polygon_area (polygon):

	if polygon and polygon[0] == polygon[-1]:
		lat_dist = math.pi * 6371009.0 / 180.0

		coord = []
		for node in polygon:
			y = node[1] * lat_dist
			x = node[0] * lat_dist * math.cos(math.radians(node[1]))
			coord.append((x,y))

		area = 0.0
		for i in range(len(coord) - 1):
			area += (coord[i+1][0] - coord[i][0]) * (coord[i+1][1] + coord[i][1])  # (x2-x1)(y2+y1)

		return area / 2.0
	else:
		return 0



# Calculate coordinate area of multipolygon, i.e. excluding inner polygons

def multipolygon_area (multipolygon):

	if type(multipolygon) is list and len(multipolygon) > 0 and type(multipolygon[0]) is list and \
			multipolygon[0][0] == multipolygon[0][-1]:

		area = polygon_area(multipolygon[0])
		for patch in multipolygon[1:]:
			inner_area = polygon_area(patch)
			if inner_area:
				area -= inner_area
			else:
				return None
		return area

	else:
		return None



# Calculate center of polygon nodes (simple average method)
# Note: If nodes are skewed to one side, the center will be skewed to the same side

def polygon_center (polygon):

	if len(polygon) == 0:
		return None
	elif len(polygon) == 1:
		return polygon[0]

	length = len(polygon)
	if polygon[0] == polygon[-1]:
		length -= 1

	x = 0
	y = 0
	for node in polygon[:length]:
		x += node[0]
		y += node[1]

	x = x / length
	y = y / length

	return (x, y)



# Calculate centroid of polygon
# Source: https://en.wikipedia.org/wiki/Centroid#Of_a_polygon

def polygon_centroid (polygon):

	if polygon[0] == polygon[-1]:
		x = 0
		y = 0
		det = 0

		for i in range(len(polygon) - 1):
			d = polygon[i][0] * polygon[i+1][1] - polygon[i+1][0] * polygon[i][1]
			det += d
			x += (polygon[i][0] + polygon[i+1][0]) * d  # (x1 + x2) (x1*y2 - x2*y1)
			y += (polygon[i][1] + polygon[i+1][1]) * d  # (y1 + y2) (x1*y2 - x2*y1)

		return (x / (3.0 * det), y / (3.0 * det) )

	else:
		return None



# Tests whether point (x,y) is inside a polygon
# Ray tracing method

def inside_polygon (point, polygon):

	if polygon[0] == polygon[-1]:
		x, y = point
		n = len(polygon)
		inside = False

		p1x, p1y = polygon[0]
		for i in range(n):
			p2x, p2y = polygon[i]
			if y > min(p1y, p2y):
				if y <= max(p1y, p2y):
					if x <= max(p1x, p2x):
						if p1y != p2y:
							xints = (y-p1y) * (p2x-p1x) / (p2y-p1y) + p1x
						if p1x == p2x or x <= xints:
							inside = not inside
			p1x, p1y = p2x, p2y

		return inside

	else:
		return None



# Test whether point (x,y) is inside a multipolygon, i.e. not inside inner polygons

def inside_multipolygon (point, multipolygon):

	if type(multipolygon) is list and len(multipolygon) > 0 and type(multipolygon[0]) is list:

		if len(multipolygon[0]) > 0 and type(multipolygon[0][0]) is list:

			for patch in multipolygon:
				if inside_multipolygon(point, patch):
					return True
			return False

		elif multipolygon[0][0] == multipolygon[0][-1]:

			inside = inside_polygon(point, multipolygon[0])
			if inside:
				for patch in multipolygon[1:]:
					inside = (inside and not inside_polygon(point, patch))
					if not inside:
						break

			return inside

		else:
			return None
	else:
		return None



# Tests whether two polygons are sharing points

def touching_polygons (p1, p2):

	p1_set = set([ (point[0], point[1]) for point in p1 ])
	p2_set = set([ (point[0], point[1]) for point in p2 ])

	return bool(p1_set & p2_set)



# Simplify line, i.e. reduce nodes within epsilon distance.
# Ramer-Douglas-Peucker method: https://en.wikipedia.org/wiki/Ramer–Douglas–Peucker_algorithm

def simplify_line(line, epsilon):

	dmax = 0.0
	index = 0
	for i in range(1, len(line) - 1):
		d = line_distance(line[0], line[-1], line[i])
		if d > dmax:
			index = i
			dmax = d

	if dmax >= epsilon:
		new_line = simplify_line(line[:index+1], epsilon)[:-1] + simplify_line(line[index:], epsilon)
	else:
		new_line = [line[0], line[-1]]

	return new_line



# Calculate new node with given distance offset in meters
# Works over short distances

def coordinate_offset (node, distance):

	m = (1 / ((math.pi / 180.0) * 6378137.0))  # Degrees per meter

	latitude = node[1] + (distance * m)
	longitude = node[0] + (distance * m) / math.cos( math.radians(node[1]) )

	return (longitude, latitude)



# Calculate Hausdorff distance, including reverse.
# Abdel Aziz Taha and Allan Hanbury: "An Efficient Algorithm for Calculating the Exact Hausdorff Distance"
# https://publik.tuwien.ac.at/files/PubDat_247739.pdf
# Amended for given maximum distance limit, to return percent of hits within given limit and to work for both polygons and lines.

def hausdorff_distance (polygon1, polygon2, limit=False, percent=False, polygon=False, hits=False):

	# Simplify polygons if needed due to size

	if percent and len(polygon1) * len(polygon2) > max_node_match:
		step = int(math.sqrt(max_node_match))
		p1 = polygon1[: -1 : 1 + len(polygon1) // step ] + [ polygon1[-1] ]
		p2 = polygon2[: -1 : 1 + len(polygon2) // step ] + [ polygon2[-1] ]
	else:
		p1 = polygon1
		p2 = polygon2

	# Start of function

	count_hits = 0
	N1 = len(p1)
	N2 = len(p2)

	if polygon:
		end = 1
	else:
		end = 0

# Shuffling for small lists disabled
#	random.shuffle(p1)
#	random.shuffle(p2)

	h = []
	cmax = 0
	for i in range(N1 - end):
		no_break = True
		cmin = 999999.9  # Dummy

		for j in range(N2 - 1):

			d = line_distance(p2[j], p2[j+1], p1[i])

			if d < cmin:
				cmin = d

			if d < cmax and not percent and not hits:
				no_break = False
				break

		if cmin < 999999.9 and cmin > cmax and no_break:
			cmax = cmin

		if limit:
			if cmin < limit:
				count_hits += 1
				if hits:
					h.append(i)					
			if not percent and not hits and cmax > limit:
				return cmax

	if hits:
		return h

	for i in range(N2 - end):
		no_break = True
		cmin = 999999.9  # Dummy

		for j in range(N1 - 1):

			d = line_distance(p1[j], p1[j+1], p2[i])

			if d < cmin:
				cmin = d

			if d < cmax and not percent:
				no_break = False
				break

		if cmin < 999999.9 and cmin > cmax and no_break:
			cmax = cmin

		if limit:
			if cmin < limit:
				count_hits +=1
			if not percent and cmax > limit:
				return cmax

	if percent:
		return [ cmax, 100.0 * count_hits / (N1 + N2 - 1 - end) ]
	else:
		return cmax



# Get bounding box for a list of coordinates

def get_bbox(coordinates, perimeter=0):

	min_bbox = ( min([point[0] for point in coordinates]), min([point[1] for point in coordinates]) )
	max_bbox = ( max([point[0] for point in coordinates]), max([point[1] for point in coordinates]) )
	if perimeter > 0:
		return coordinate_offset(min_bbox, - perimeter), coordinate_offset(max_bbox, + perimeter)
	else:
		return min_bbox, max_bbox



# Get name or id of municipality from GeoNorge api

def get_municipality_name (query):

	if query.isdigit():
		url = "https://ws.geonorge.no/kommuneinfo/v1/kommuner/" + query
	else:
		url = "https://ws.geonorge.no/kommuneinfo/v1/sok?knavn=" + urllib.parse.quote(query)

	request = urllib.request.Request(url, headers=header)

	try:
		file = urllib.request.urlopen(request)
	except urllib.error.HTTPError as e:
		if e.code == 404:  # Not found
			sys.exit("\tMunicipality '%s' not found\n\n" % query)
		else:
			raise

	if query.isdigit():
		result = json.load(file)
		file.close()
		municipality_name = result['kommunenavnNorsk']
		bbox = get_bbox(result['avgrensningsboks']['coordinates'][0])
		return (query, municipality_name, bbox)

	else:
		result = json.load(file)
		file.close()
		if result['antallTreff'] == 1:
			municipality_id = result['kommuner'][0]['kommunenummer']
			municipality_name = result['kommuner'][0]['kommunenavnNorsk']
			bbox = get_bbox(result['kommuner'][0]['avgrensningsboks']['coordinates'][0])
			return (municipality_id, municipality_name, bbox)
		else:
			municipalities = []
			for municipality in result['kommuner']:
				municipalities.append(municipality['kommunenummer'] + " " + municipality['kommunenavnNorsk'])
			sys.exit("\tMore than one municipality found: %s\n\n" % ", ".join(municipalities))



# Clean Norwegian characters from filename

def clean_filename(filename):

	return filename.replace("Æ","E").replace("Ø","O").replace("Å","A").replace("æ","e").replace("ø","o").replace("å","a").replace(" ", "_")



# Load municipality boundary polygon

def load_municipality_boundary():

	global municipality_border

	# Load boundary

	url = "https://ws.geonorge.no/kommuneinfo/v1/kommuner/%s/omrade" % municipality_id
	request = urllib.request.Request(url, headers=header)
	file = urllib.request.urlopen(request)
	boundary_data = json.load(file)
	file.close()

	# Get full boundary, incl. exclaves and enclaves

	municipality_border = []

	for patch in boundary_data['omrade']['coordinates']:  # Incl. exclaves/multiple polygons (Kinn, Ålesund)
		patches = []
		for boundary in patch:  # Incl. enclaves
			polygon = [ tuple(point) for point in boundary ]  # Get tuples
			patches.append( simplify_line(polygon, 1) )
		municipality_border.append(patches)

	return

	# Load boundary file

	boundary_url = "https://nedlasting.geonorge.no/geonorge/Basisdata/Kommuner/GeoJSON/"
	boundary_filename = "Basisdata_%s_%s_4258_Kommuner_GeoJSON" % (municipality_id, municipality_name)
	boundary_filename = clean_filename(boundary_filename)

	request = urllib.request.Request(boundary_url + boundary_filename + ".zip", headers=header)
	file_in = urllib.request.urlopen(request)
	zip_file = zipfile.ZipFile(BytesIO(file_in.read()))
	file = zip_file.open(boundary_filename + ".geojson")
	boundary_data = json.load(file)
	file.close()
	file_in.close()

	# Get full boundary, incl. exclaves and enclaves

	municipality_border = []

	for feature in boundary_data['Kommune']['features']:  # Incl. exclaves/multiple polygons (Kinn, Ålesund)
		patches = []
		for boundary in feature['geometry']['coordinates']:  # Incl. enclaves
			polygon = [ ( point[0], point[1] ) for point in boundary ]  # Get tuples
			patches.append( simplify_line(polygon, 1) )
		municipality_border.append(patches)

	# Get list of boundary segments

	for boundary_type, boundary_collection in iter(boundary_data.items()):
		if any(name in boundary_type for name in ["Grense", "kommunegrense", "fylkesgrense", "riksgrense"]):  # Boundary segments
			for boundary in boundary_collection['features']:
				polygon = [ ( point[0], point[1] ) for point in boundary['geometry']['coordinates'] ]  # Get tuples
				boundary['geometry']['coordinates'] = simplify_line(polygon, 1)
			municipality_border_segments.extend(boundary_collection['features'])

	return municipality_border



# Check if line is close to municipality_border

def close_to_border(line, limit):

	d = line_length(line)

	for patch in municipality_border:
		for polygon in patch:
			for point in line:
				distance, node_index = shortest_distance(point, polygon)
				if distance <= limit:
					return True
				elif distance > d:  # Exclude impossible iterations
					break

	return False



# Get tags of OSM or N50 element

def get_tags(xml_element):

	tags = {}
	for tag in xml_element.findall("tag"):
		tags[ tag.attrib['k'] ] = tag.attrib['v']	

	return tags



# Create new OSM element id

def new_id():

	global osm_identifier

	if "osm_identifier" in globals():
		osm_identifier -= 1
		return osm_identifier

	else:
		osm_identifier = min(min(element['id'] for element in elements) // 10000 * 10000, -10000) - 1
		return osm_identifier



# Create feature with one point

def create_point (node, tags, parent=None):

	for key in list(tags):
		if key in ["N50", "N100"]:
			del tags[ key ]

	element = {
		'type': 'node',
		'id': new_id(),
#		'action': 'modify',
		'lat': node[1],
		'lon': node[0],
		'tags': tags,
		'parents': set()
	}
	if parent is not None:
		element['parents'].add(parent)

	elements.append(element)
	nodes[ element['id'] ] = element

	return element['id']



# Determine keywords used for matching

def get_topo_type(element):

	tags = element['tags']
	topo_type = set()
	if "natural" in tags:
		if tags['natural'] == "water" and "water" in tags and tags['water'] == "river":
			if "intermittent" in tags:
				topo_type.add("intermittent")  # "Tørrfall"
			else:
				topo_type.add("river")
		else:
			topo_type.add(tags['natural'])	# Including oxbow
	if "landuse" in tags:
		if tags['landuse'] == "forest":
			topo_type.add("wood")
		elif tags['landuse'] in ["meadow", "grass"]:
			topo_type.add("farmland")
		else:
			topo_type.add(tags['landuse'])
	if "waterway" in tags and element['type'] == "way":
		if tags['waterway'] == "riverbank":
			topo_type.add("river")
		elif tags['waterway'] in ["river", "stream", "ditch", "canal"] and "tunnel" not in tags:
			topo_type.add("stream")
		else:
			topo_type.add(tags['waterway'])
	if "leisure" in tags and element['tags']['leisure'] in ["pitch", "track"]:
		topo_type.add(element['tags']['leisure'])		
	if "place" in tags and tags['place'] in ["islet", "island"]:
		topo_type.add("island")
	if "piste:type" in tags and tags['piste:type'] in "downhill":
		topo_type.add("winer_sports")
	return topo_type



# Merge new tags into existing tax

def merge_tags (feature, new_tags, overwrite=True):

	for key, value in iter(new_tags.items()):
		if (key in ["source:date", "created_by", "N50", "N100"]
				or key == "source" and any(word in value for word in disregard_sources)):
			continue

		if key == "FIXME" and "FIXME" in feature['tags']:
			if value not in feature['tags']['FIXME']:
				feature['tags']['FIXME'] += "; " + value
				feature['action'] = "modify"
		else:
			if key in feature['tags']:
				if feature['tags'][ key ] != value:
					if overwrite:
						feature['tags'][ "OSM_" + key ] = feature['tags'][ key ]
						feature['tags'][ key ] = value
					else:
						feature['tags'][ "OSM_" + key ] = value
					feature['action'] = "modify"
			else:
				feature['tags'][ key ] = value
				feature['action'] = "modify"


# Delete nodes in way + set way attributes for deletion.
# Any relation members using this way must be updated outside of this function.

def delete_way (way):

	# Remove surplus nodes

	for node_id in way['nodes']:
		node = nodes[ node_id ]
		if way['id'] in node['parents']:
			node['parents'].remove(way['id'])
		if not node['parents']:
			node['action'] = "delete"

	way['nodes'] = []
	way['action'] = "delete"
	way['incomplete'] = True

	if "topo" in way:
		way['topo'] = set()

	if "coordinates" in way:
		del way['coordinates']



# Get and display top contributors

def top_contributors():

	users = {}
	for element in elements:
		if "user" in element and element['type'] in ["way", "relation"]:
			if element['user'] not in users:
				users[ element['user'] ] = 0
			users[ element['user'] ] += 1

	sorted_users = sorted(users.items(), key=lambda x: x[1], reverse=True)

	message ("\tTop contributors:\n")
	for i, user in enumerate(sorted_users):
		if user[1] > 10 and i < 10 or user[1] >= 100:
			message ("\t\t%s (%i)\n" % (user[0], user[1]))



# Load relevant OSM elements for chosen municipality

def load_osm_overpass():

	global elements

	message ("Load existing OSM elements from Overpass ...\n")

	area_query = '[ref=%s][admin_level=7][place=municipality]' % municipality_id

	query = ('[out:json][timeout:200];'
				'(area%s;)->.a;'
				'('
					'nwr["natural"](area.a);'
					'nwr["waterway"](area.a);'
					'nwr["landuse"](area.a);'
					'nwr["leisure"]["leisure"!="nature_reserve"](area.a);'
					'nwr["aeroway"](area.a);'
					'nwr["man_made"](area.a);'
					'nwr["piste:type"="downhill"](area.a);'
					'nwr["seamark:type"="rock"](area.a);'				
				');'
				'(._;>;<;);'
				'out meta;' % area_query)

	request = urllib.request.Request(overpass_api + "?data=" + urllib.parse.quote(query), headers=header)
	try:
		file = urllib.request.urlopen(request)
	except urllib.error.HTTPError as err:
		sys.exit("\n\t*** %s\n\n" % err)
	data = json.load(file)
	elements = data['elements']
	file.close()

	prepare_data()

	message ("\tLoaded %i ways, %i relations\n" % (len(ways), len(relations)))

	top_contributors()


# Load OSM elements from file

def load_osm_file(filename):

	message ("Load existing OSM elements from '%s' file ...\n" % filename)	

	if not os.path.isfile(filename):
		sys.exit ("\n*** File not found\n\n")

	file = open(filename)
	data = file.read()
	file.close()

	root = ET.fromstring(data)
	tree = ET.ElementTree(root)

	for osm_element in root:
		element = {
			'type': osm_element.tag,
			'tags': {}
		}
		if osm_element.tag == "way":
			element['nodes'] = []
		elif osm_element.tag == "relation":
			element['members'] = []

		for key in osm_element.attrib:
			if key in ["id", "version", "changeset", "uid"]:
				element[ key ] = int(osm_element.attrib[ key ])
			elif key in ["lat", "lon"]:
				element[ key ] = float(osm_element.attrib[ key ])
			else:
				element[ key ] = osm_element.attrib[ key ]

		for child in osm_element:
			if child.tag == "tag":
				element['tags'][ child.attrib['k'] ] = child.attrib['v']
			elif child.tag == "nd":
				element['nodes'].append( int(child.attrib['ref']) )
			elif child.tag == "member":
				member = {
					'type': child.attrib['type'],
					'ref': int(child.attrib['ref']),
					'role': child.attrib['role']
				}
				element['members'].append(member)
		elements.append(element)

	prepare_data()

	message ("\tLoaded %i ways, %i relations\n" % (len(ways), len(relations)))

	top_contributors()



# Build dict data structure from XML.

def prepare_data ():

	# Make sure tags dict is present

	for element in elements:
		if "tags" not in element:
			element['tags'] = {}

	# Create dict of nodes
	# Each node is a tuple of (lon, lat), corresponding to GeoJSON format x,y

	for node in elements:
		if node['type'] == "node" and not ("action" in node and node['action'] == "delete"):

			nodes[ node['id'] ] = node
			node['parents'] = set()  # Built in next loop

	# Create dict of ways

	for way in elements:
		if way['type'] == "way" and not ("action" in way and way['action'] == "delete"):

			way_coordinates = []
			incomplete = False

			# Get way nodes + determine if way is complete

			for node_id in way['nodes']:
				if node_id in nodes:
					node = nodes[ node_id ]
					way_coordinates.append(( node['lon'], node['lat'] ))
					nodes[ node_id ]['parents'].add(way['id'])
				else:
					incomplete = True

			if incomplete:
				way_coordinates = []

			ways[ way['id'] ] = way
			way['incomplete'] = incomplete
			way['coordinates'] = [ way_coordinates ]  # Multipolygon style
			way['parents'] = set()  # Built in next loop
			if incomplete:
				way['topo'] = set()
			else:
				way['topo'] = get_topo_type(way)

	# Create dict of relations

	for relation in elements:
		if relation['type'] == "relation" and not ("action" in relation and relation['action'] == "delete"):

			island = "place" in relation['tags'] and relation['tags']['place'] in ["islet", "island"]  # Identify relations which are islands
			incomplete = False
			members = []

			for member in relation['members']:
				members.append(member['ref'])
				if member['ref'] in ways:
					ways[ member['ref'] ]['parents'].add(relation['id'])  # Incomplete members will be missing
					if ways[ member['ref'] ]['incomplete']:
						incomplete = True
				else:
					incomplete = True
				if member['type'] in ["node", "relation"]:
					if member['ref'] in nodes:
						nodes[ member['ref'] ]['parents'].add(relation['id'])
					incomplete = True

			if members:
				relations[ relation['id'] ] = relation
				relation['incomplete'] = incomplete
				relation['member_list'] = members
				if incomplete:
					relation['topo'] = get_topo_type(relation)
				else:
					relation['topo'] = get_topo_type(relation)



# Check if a relation is a grid.
# Stores an x,y type grid identifier, or None.
# Each grid is 0.05 degrees.

def check_grid(relation):

	count_edge = 0
	bbox_list = []
	for member in relation['members']:
		way = ways[ member['ref'] ]
		coordinates = way['coordinates'][0]
		min_bbox, max_bbox = get_bbox(coordinates)
		bbox_list.extend([ min_bbox, max_bbox ])

		if (abs(coordinates[0][0] - coordinates[-1][0]) < grid_limit
		 		and abs(coordinates[0][0] - round(coordinates[0][0] * 20) / 20) < grid_limit
		 		and (len(way['nodes']) == 2 or abs(max_bbox[0] - min_bbox[0]) < grid_limit)):
			way['grid'] = "lon"
			count_edge +=1
		elif (abs(coordinates[0][1] - coordinates[-1][1]) < grid_limit
				and abs(coordinates[0][1] - round(coordinates[0][1] * 20) / 20) < grid_limit
				and (len(way['nodes']) == 2 or abs(max_bbox[1] - min_bbox[1]) < grid_limit)):
			way['grid'] = "lat"
			count_edge += 1

	if count_edge == 0:
		if "grid" in relation:
			del relation['grid']
	else:
		min_bbox, max_bbox = get_bbox(bbox_list)

		if max_bbox[0] - min_bbox[0] > 0.075 or max_bbox[1] - min_bbox[1] > 0.075:  # More than 50% larger than grid
			relation['grid'] = "grid"
		else:
			center = [ 0.5 * (min_bbox[0] + max_bbox[0]), 0.5 * (min_bbox[1] + max_bbox[1]) ]
			relation['grid'] = ( int(20 * center[0]), int(20 * center[1]) )



# Create list of tagged objects which are closed/ring to prepare for later matching and merging

def prepare_features ():

	# Get all ways which are closed rings

	for way in ways.values():
		coordinates = way['coordinates'][0]
		if (not way['incomplete'] and way['tags'] and not coordinates):
			message (str(way))
		if (not way['incomplete']
				and  way['tags'] and coordinates[0] == coordinates[-1]):
			min_bbox, max_bbox = get_bbox(coordinates)
			area = abs(polygon_area(coordinates))
			if area > 0:
				way['area'] = area
				way['min_bbox'] = min_bbox
				way['max_bbox'] = max_bbox 
				features.append(way)

	# Get all relations which are closed rings

	count_grid = 0

	for relation in relations.values():
		if not relation['incomplete'] and relation['tags'] and "coordinates" in relation:

			if not relation['coordinates']:
				message (str(relation))
			min_bbox, max_bbox = get_bbox(relation['coordinates'][0])  # Outer
			area = abs(multipolygon_area(relation['coordinates']))
			if area > 0:
				relation['area'] = area
				relation['min_bbox'] = min_bbox
				relation['max_bbox'] = max_bbox 
				features.append(relation)

			# Identify wood grid

			if relation['topo'] == set(["wood"]):
				check_grid(relation)
				if "grid" in relation:
					count_grid += 1

	message ("\tIdentified %i area features\n" % len(features))
	message ("\tIdentified %i wood grids\n" % count_grid)



# Reorder members of OSM relations if needed.
# Necessary for correct manipulation of relation members.
# Check paramter if only for checking correct order, but no amendments.

def fix_relation_order():

	count_fix = 0

	for relation in relations.values():

		if relation['topo'] and not relation['incomplete']:
			old_members = copy.deepcopy(relation['members'])
			fix_member_order(relation)
			if relation['members'] != old_members:
				relation['tags']['REORDER'] = "yes"
				relation['action'] = "modify"
				count_fix += 1
				if len(relation['member_patches']) > 1 and relation['member_patches'][1][0]['role'] != "inner":
					del relation['coordinates']
					relation['tags']['OUTER'] = "Multiple outer areas"
					message ("\t*** Multiple outer areas in relation %s\n" % relation['id'])

	message ("\t%i relations reordered\n" % count_fix)



# Reorder members of OSM relation if needed.
# Necessary for correct manipulation of relation members.
# Check paramter if only for checking correct order, but no amendments.

def fix_member_order(relation):

	# Identify each ring and build list of rings (patches)

	remaining_members = copy.deepcopy(relation['members'])
	polygon_patches = []
	found = True

	while remaining_members and found:
		if ways[ remaining_members[0]['ref'] ]['incomplete']:
			break
		coordinates = copy.copy(ways[ remaining_members[0]['ref'] ]['coordinates'][0])
		patch = [ remaining_members[0] ]
		start_member = patch[0]
		remaining_members.pop(0)
		patch_direction = 1
		found = True

		# Keep adding members as long as they match end-to-end

		while found:
			found = False
			for member in remaining_members:
				if not ways[ member['ref'] ]['incomplete']:
					member_coordinates = ways[ member['ref'] ]['coordinates'][0]
					if coordinates[-1] == member_coordinates[0]:
						coordinates.extend(member_coordinates[1:])
						patch.append(member)
						direction = 1
					elif coordinates[-1] == member_coordinates[-1]:
						coordinates.extend(list(reversed(member_coordinates))[1:])
						patch.append(member)
						direction = -1
					else:
						continue

					patch_direction += direction
					remaining_members.remove(member)
					found = True
					break

		if coordinates[0] == coordinates[-1]:
			polygon_patch = {
				'members': patch,
				'coordinates': coordinates
			}
			polygon_patches.append(polygon_patch)
			found = True

	if not remaining_members:

		# Sort outer before inner
		i = 0
		for patch in polygon_patches[:]:	
			if patch['members'][0]['role'] == "outer":
				polygon_patches.remove(patch)
				polygon_patches.insert(i, patch)
				i += 1

		new_member_order = [ member for patch in polygon_patches for member in patch['members'] ]  # Flat, ordered member list

		if new_member_order != relation['members']:

			# Outer members in clockwise direction, inner in anti-clockwise (coastline method)
			for patch in polygon_patches:
				area = polygon_area(patch['coordinates'])
				if patch['members'][0]['role'] == "outer" and area < 0 or patch['members'][0]['role'] == "inner" and area > 0:
					patch['members'] = [ patch['members'][0] ] + list(reversed(patch['members'][1:]))

			new_member_order = [ member for patch in polygon_patches for member in patch['members'] ]
			if new_member_order != relation['members']:
				relation['action'] = "modify"

		relation['coordinates'] = [ patch['coordinates'] for patch in polygon_patches ]
		relation['member_patches'] = [ patch['members'] for patch in polygon_patches ]
		relation['members'] = new_member_order  # Rearranged order

	else:
		if "coordinates" in relation:
			del relation['coordinates']



# Identify and remove overlapping ways.
# Likely caused by simplification of ways for water and wood/landuse run separately.
# Water ways may have extra node due to intersection with waterway.

def fix_overlapping_ways ():

	message ("Fix overlapping ways ...\n")

	# Part 1: Merge overlapping ways between same type relations (typically at municipality boundary)

	count = 0
	check_members = []

	for feature in features:
		if feature['type'] == "relation":
			for member in feature['members']:
				way = ways[ member['ref'] ]
				parents = list(way['parents'])
				if len(parents) == 1:
					check_members.append(way)
					way['min_bbox'], way['max_bbox'] = get_bbox(way['coordinates'][0])

	# Then match against each other to find close fit

	count_down = len(check_members)
	for i, way1 in enumerate(check_members):

		count_down -= 1
		if count_down % 100 == 0:
			message ("\r\t%i " % count_down)

		relation1 = relations[ list(way1['parents'])[0] ]

		if way1['incomplete']:
			continue

		best_way = None
		best_relation = None
		best_gap = 5

		for way2 in check_members[i+1:]:
			relation2 = relations[ list(way2['parents'])[0] ] 

			if (not way2['incomplete'] and relation1 != relation2
					and relation1['topo'] == relation2['topo']
					and (way1['min_bbox'][0] <= way2['max_bbox'][0] and way1['max_bbox'][0] >= way2['min_bbox'][0]
					and way1['min_bbox'][1] <= way2['max_bbox'][1] and way1['max_bbox'][1] >= way2['min_bbox'][1])
					and ("grid" in way1) == ("grid" in way2)
					and (way1['nodes'][0] == way1['nodes'][-1]) == (way2['nodes'][0] == way2['nodes'][-1])):  # Xor):

				gap = hausdorff_distance(way1['coordinates'][0], way2['coordinates'][0], limit=5)
				if gap < best_gap:
					best_way = way2
					best_gap = gap

		# Swap ways

		if best_gap < 5:
			way1['tags']['OVERLAP'] = "yes"
			swap_ways(way1, best_way)
			count += 1


	# Part 2: Merge overlapping ways of any type

	# Build list of ways to compare

	check_ways = []

	for feature in features:
		if feature['topo']:  # "water" in feature['topo'] or "river" in feature['topo']:
			if feature['type'] == "way":
				if (all(parent_id in relations and not relations[ parent_id ]['incomplete'] and "coordinates" in relations[ parent_id ]
							for parent_id in feature['parents'])
						and "OVERLAP" not in feature['tags']):
					check_ways.append(feature)
					feature['min_bbox'], feature['max_bbox'] = get_bbox(feature['coordinates'][0])
			else:
				for member in feature['members']:
					way = ways[ member['ref'] ]
					if (all(parent_id in relations and not relations[ parent_id ]['incomplete'] and "coordinates" in relations[ parent_id ]
								for parent_id in way['parents'])
							and "grid" not in way
							and "OVERLAP" not in way['tags']):
						check_ways.append(way)
						way['min_bbox'], way['max_bbox'] = get_bbox(way['coordinates'][0])

	# Add coastline ways

	for way in ways.values():
		if ("topo" in way
				and "coastline" in way['topo']
				and not way['incomplete']
				and way not in check_ways
				and "OVERLAP" not in way['tags']
				and (all(parent_id in relations and not relations[ parent_id ]['incomplete'] and "coordinates" in relations[ parent_id ]
						for parent_id in way['parents']))):
			check_ways.append(way)
			way['min_bbox'], way['max_bbox'] = get_bbox(way['coordinates'][0])

	# Mark way if any intersections with waterways

	for way in check_ways:
		stream_nodes = 0
		for node_id in way1['nodes']:
			for parent_id in nodes[ node_id ]['parents']:
				if parent_id in ways and "stream" in ways[ parent_id ]['topo']:
					stream_nodes += 1
					break
		if stream_nodes > 0:
			way['streams'] = stream_nodes

	# Alternative

	count_down = len(check_ways)
	for i, way1 in enumerate(check_ways):

		count_down -= 1
		if count_down % 100 == 0:
			message ("\r\t%i " % count_down)

		way_set1 = set(way1['nodes'])
		best_way = None
		best_gap = 5  # Dummy

		# Check overlap with other topo ways/members
		if not way1['incomplete'] and "OVERLAP" not in way1['tags']:

			connected_ways = nodes[ way1['nodes'][0] ]['parents'] & nodes[ way1['nodes'][-1] ]['parents'] - set([way1['id']])

			for way2_id in connected_ways:
				if way2_id not in ways:
					continue
				way2 = ways[ way2_id ]
				if way2 not in check_ways:
					continue

				if (not way2['incomplete']
						and not (way1['parents'] & way2['parents'])):

					gap = hausdorff_distance(way1['coordinates'][0], way2['coordinates'][0], limit=5)
					if gap < best_gap:
						best_way = way2
						best_gap = gap

			# Swap ways

			if (best_gap < 5
					and (way1['nodes'][0] == way1['nodes'][-1]) == (best_way['nodes'][0] == best_way['nodes'][-1])
					and "OVERLAP" not in best_way['tags']):

				# Keep way with stream connections or way with most nodes

				from_way, to_way = best_way, way1

				if "coastline" not in to_way['topo'] and ("streams" not in to_way or "coastline" in from_way['topo']):
					if ("coastline" in from_way['topo']
							or "streams" in from_way
							or len(from_way['nodes']) > len(to_way['nodes'])):
						from_way, to_way = to_way, from_way

				to_way['tags']['OVERLAP'] = "yes"
				merge_tags(to_way, from_way['tags'], overwrite=False)
				swap_ways(to_way, from_way)
				count += 1	

	message ("\r\tMerged %i overlapping ways\n" % count)



# Swap way2 with way1 (latter survives).
# End nodes are merged and parent relations updated.

def swap_ways(way1, way2):

	# Merge end nodes

	if distance(way1['coordinates'][0][0], way2['coordinates'][0][0]) < distance(way1['coordinates'][0][0], way2['coordinates'][0][-1]):
		swaps = [(0, 0), (-1,-1)]
	else:
		swaps = [(0, -1), (-1, 0)]

	for from_index, to_index in swaps:
		from_node = nodes[ way2['nodes'][ from_index ] ]
		to_node = nodes[ way1['nodes'][ to_index ] ]
		if from_node != to_node:

			for way_parent_id in from_node['parents']:
				way_parent = ways[ way_parent_id ]
				for j, node_id in enumerate(way_parent['nodes']):
					if node_id == from_node['id']:
						way_parent['nodes'][ j ] = to_node['id']
						way_parent['action'] = "modify"

			from_node['action'] = "delete"
			from_node['parents'] = set()
			to_node['parents'].add(way2['id'])

			way2['nodes'][ from_index ] = way1['nodes'][ to_index ]
			way2['coordinates'][0][ from_index ] = way1['coordinates'][0][ to_index ]

	# Delete way2 and middle nodes

	delete_way(way2)
	way1['action'] = "modify"

	# Update parent relations of way2

	for relation_id in way2['parents']:
		relation = relations[ relation_id ]
		for member in relation['members']:
			if member['ref'] == way2['id']:
				member['ref'] = way1['id']
				way1['parents'].add(relation_id)

		for patch in relation['member_patches']:
			for member in patch:
				if member['ref'] == way2['id']:
					member['ref'] = way1['id']

		relation['action'] = "modify"

	# Check if any remaining void ways due to node relocation

	for end in [0, -1]:
		for way_id in list(nodes[ way1['nodes'][ end ] ]['parents']):
			way = ways[ way_id ]
			if way != way1 and len(way['nodes']) == 2 and way['nodes'][0] == way['nodes'][-1]:
				delete_way(way)

				for relation_id in way['parents']:
					relation = relations[ relation_id ]
					for member in relation['members'][:]:
						if member['ref'] == way['id']:
							relation['members'].remove(member)
							relation['action'] = "modify"

					if "member_patches" in relation:  # Incomplete relations may not have patches
						for patch in relation['member_patches'][:]:
							for member in patch[:]:
								if member['ref'] == way['id']:
									patch.remove(member)
							if not patch:
								relation['member_patches'].remove(patch)



# Step 1 of splitting/merging relations.
# Discover relations of same topo type with common way.
# Add FIXME=Merge on common members for further manual adjustments in JOSM.

def identify_touching_relations(merge_grids=False):

	lap_time = time.time()
	message ("Discover touching topo relations ...\n")

	# Part 1: Check relation members with two parents

	count_merge = 0

	for feature in features:
		if feature['type'] == "relation":
			for member in feature['members'][:]:
				way = ways[ member['ref'] ]
				parents = list(way['parents'])
				if len(parents) != 2:
					continue

				relation1 = relations[ parents[0] ]
				relation2 = relations[ parents[1] ]

				if (relation1['incomplete'] and relation2['incomplete']
						or not merge_grids and (relation1['incomplete'] or relation2['incomplete'])
						or relation1['topo'] != relation2['topo']
						or not any(topo in relation1['topo'] for topo in ["water", "river", "wetland", "landuse", "wood"])):
					continue

				if (relation1['topo'] == set(["wood"])
						and ("grid" in ways[ member['ref'] ]
							or not merge_grids and "grid" in relation1 and "grid" in relation2
								and (relation1['grid'] != relation2['grid']
									or relation1['grid'] == "grid"))):  # Avoid merging wood grids
					continue

				if "FIXME" in way['tags'] and way['tags']['FIXME'] not in ["Merge", "Join"]:
					way['tags']['OSM_FIXME'] = way['tags']['FIXME']

				if relation1['incomplete'] or relation2['incomplete']:
					way['tags']['FIXME'] = "Merge incomplete"
				elif "grid" in way:
					way['tags']['FIXME'] = "Merge grid"
				else:
					way['tags']['FIXME'] = "Merge"
				way['action'] = "modify"

				count_merge += 1

	# Part 2: Check (almost) overlapping relation members
	# First find members with only one parent

	count_join = 0
	check_members = []

	for feature in features:
		if feature['type'] == "relation":
			for member in feature['members']:
				way = ways[ member['ref'] ]
				parents = list(way['parents'])
				if len(parents) == 1:
					check_members.append(member['ref'])
					way['min_bbox'], way['max_bbox'] = get_bbox(way['coordinates'][0])

	# Then match against each other to find close fit

	count_down = len(check_members)
	for i, way_id1 in enumerate(check_members):

		count_down -= 1
		if count_down % 100 == 0:
			message ("\r\t%i " % count_down)

		way1 = ways[ way_id1 ]
		relation1 = relations[ list(way1['parents'])[0] ]

		if way1['incomplete']:
			continue

		best_way = None
		best_relation = None
		best_gap = 5

		for way_id2 in check_members[i+1:]:
			way2 = ways[ way_id2]
			relation2 = relations[ list(way2['parents'])[0] ] 

			if (not way2['incomplete'] and relation1 != relation2
					and relation1['topo'] == relation2['topo']
					and (way1['min_bbox'][0] <= way2['max_bbox'][0] and way1['max_bbox'][0] >= way2['min_bbox'][0]
					and way1['min_bbox'][1] <= way2['max_bbox'][1] and way1['max_bbox'][1] >= way2['min_bbox'][1])):

				gap = hausdorff_distance(way1['coordinates'][0], way2['coordinates'][0], limit=5)
				if gap < best_gap:
					best_way = way2
					best_gap = gap

		# Swap ways

		if best_gap < 5:
			if "FIXME" in way1['tags']:
				way1['tags']['OSM_FIXME'] = way1['tags']['FIXME']
			way1['tags']['FIXME'] = "Join"
			swap_ways(way1, best_way)
			count_join += 1

	message ("\r\tIdentified %i relations for merging and %i for joining\n" % (count_merge, count_join))
	message ("\tRun time %i seconds\n" % (time.time() - lap_time))



# Recursive function for identifying smalles closed area defined by 'permitted_members' argument.
# - end_nodes: Way end nodes (id's) visited so far. Last node to be processed.
# - members: Ways (id's) visited so far. Last member to be processed.
# - coordinates: Ring so far.
# - permitted_members: Ways (id's) which may be included in ring.
# Returns members of ring, area of ring and ring coordinates.

def get_smallest_area(end_nodes, members, coordinates, permitted_members):

	# Determine next node

	if ways[ members[-1] ]['nodes'][0] == end_nodes[-1]:
		next_node = ways[ members[-1] ]['nodes'][-1]
		new_coordinates = coordinates + ways[ members[-1] ]['coordinates'][0][1:]
	else:
		next_node = ways[ members[-1] ]['nodes'][0]
		new_coordinates = coordinates + list(reversed(ways[ members[-1] ]['coordinates'][0]))[1:]

	# Check if ring is complete

	if next_node == end_nodes[0]:
		new_coordinates.append(new_coordinates[0])  # Ring
		area = abs(polygon_area(new_coordinates))
		return members, area, new_coordinates

	smallest_area = 0
	smallest_members = []
	smallest_coordinates = []

	# Recursively test all branches at intersections and keep ring with smallest area

	for test_member in nodes[ next_node ]['parents']:
		if test_member not in members and test_member in permitted_members and next_node not in end_nodes[1:]:
			full_members, area, full_coordinates = get_smallest_area(end_nodes + [ next_node ], members + [ test_member ], new_coordinates, permitted_members)
			if area > 0 and (smallest_area == 0 or area < smallest_area):
				smallest_area = area
				smallest_members = full_members
				smallest_coordinates = full_coordinates

	return smallest_members, smallest_area, smallest_coordinates



# Step 2 of splitting/merging relations.
# First split relations as indicated by FIXME=Split tag on new connected ways.
# Then merge relations as indicated by FIXME=Merge tag on common ways.

def merge_touching_relations():

	message ("Discover touching topo relations ...\n")
	count_split = 0
	count_split_new = 0
	count_merge = 0

	# Step 1: Split
	# Identify ways tagged with Split

	split_relations = {}

	for way in ways.values():
		if "FIXME" in way['tags'] and way['tags']['FIXME'] == "Split" and not way['incomplete'] and way['nodes'][0] != way['nodes'][-1]:
			parents1 = set.union(*[ ways[ parent_ways ]['parents'] for parent_ways in nodes[ way['nodes'][0] ]['parents'] ])
			parents2 = set.union(*[ ways[ parent_ways ]['parents'] for parent_ways in nodes[ way['nodes'][-1] ]['parents'] ])
			parent_relations = list(parents1 & parents2)

			# Exclude any boundary relations
			for relation_id in parent_relations[:]:
				if relation_id in relations:				
					relation = relations[ relation_id ]
					if "boundary" in relation['tags'] or "was:boundary" in relation['tags']:
						parent_relations.remove(relation_id)
						message ("\t* Excluded boundary relation %i\n" % relation_id)


			# Exclude relations outside of way position
			if len(parent_relations) > 1:
				if len(way['nodes']) == 2:
					test_point = ( 0.5 * (nodes[ way['nodes'][0] ]['lon'] + nodes[ way['nodes'][-1] ]['lon']),
									 0.5 * (nodes[ way['nodes'][0] ]['lat'] + nodes[ way['nodes'][-1] ]['lat']) )
				else:
					test_point = (nodes[ way['nodes'][ len(way['nodes']) // 2 ] ]['lon'],
									nodes[ way['nodes'][ len(way['nodes']) // 2 ] ]['lat'] )
				for relation_id in parent_relations[:]:
					if relation_id in relations:
						relation = relations[ relation_id ]
						if not inside_multipolygon(test_point, relation['coordinates']) is True:
							parent_relations.remove(relation_id)

			# Store in split list if split is possible
			if len(parent_relations) != 1:
				message ("\t*** Split undetermined for way %s\n" % way['id'])
				way['tags']['NO_SPLIT'] = "Split undetermined"
			elif parent_relations[0] not in relations or relations[ parent_relations[0] ]['incomplete'] or "coordinates" not in relations[ parent_relations[0] ]:
				message ("\t*** Relation incomplete: %s\n" % parent_relations[0])
				way['tags']['NO_SPLIT'] = "Relation incomplete"
			else:				
				if parent_relations[0] not in split_relations:
					split_relations[ parent_relations[0] ] = []
				split_relations[ parent_relations[0] ].append(way['id'])

	# Split each relation

	for relation_id, split_relation_members in iter(split_relations.items()):

		old_relation = relations[ relation_id ]
		outer_members = [ member['ref'] for member in old_relation['member_patches'][0] ]
		inner_members = [ member['ref'] for patch in old_relation['member_patches'][1:] for member in patch ]
		split_members = split_relation_members.copy()
		new_relations = []
		area = 1  # Dummy

		# Keep checking all possible closed areas until all outer members have been exhausted

		while area > 0 and outer_members:
			remaining_members = outer_members + split_relation_members + inner_members  # Note: order is important
			node = ways[ remaining_members[0] ]['nodes'][0]
			area_members, area, coordinates = get_smallest_area([ node ], [ remaining_members[0] ], [], remaining_members)

			if area > 0:
				new_relation = {
					'members': area_members,
					'area': area,
					'coordinates': coordinates
				}
				new_relations.append(new_relation)
				for member in area_members:
					if member in outer_members:
						outer_members.remove(member)
					elif member in inner_members:
						inner_members.remove(member)

		if outer_members:
			message ("\t*** Remaining outer members after splitting relation %i:\n\t\t%s\n" % (relation_id, str(outer_members)))
			continue

		new_relations.sort(key=lambda relation: relation['area'], reverse=True)  # Largest first

		for member in old_relation['members']:
			ways[ member['ref' ] ]['parents'].remove(old_relation['id'])

		# Add/update relations and members
		# Note: More than one new relation may have been identified.

		for i, new_relation in enumerate(new_relations):
			new_feature = {
				'type': 'relation',
				'tags': copy.deepcopy(old_relation['tags']),
				'members': [],
				'topo': old_relation['topo'].copy(),
				'incomplete': False
			}

			# Add outer members
			for member in new_relation['members']:
				new_member = {
					'type': 'way',
					'ref': member,
					'role': 'outer'
				}
				new_feature['members'].append(new_member)

				way = ways[ member ]
				if "FIXME" in way['tags'] and way['tags']['FIXME'] == "Split":  # Remove FIXME tag
					del way['tags']['FIXME']
					way['tags']['SPLIT'] = "yes"
					way['action'] = "modify"

			# Add inner members
			for member in inner_members[:]:
				if inside_polygon(ways[ member ]['coordinates'][0][1], new_relation['coordinates']):
					new_member = {
						'type': 'way',
						'ref': member,
						'role': 'inner'
					}
					new_feature['members'].append(new_member)
					inner_members.remove(member)

			# Wrap up settings for relation

			new_feature['tags']['SPLIT'] = "yes"
			new_feature['action'] = "modify"

			if i == 0:
				old_relation.update(new_feature)  # Largest relation inherits old id
				new_feature = old_relation
			else:
				new_feature['id'] = new_id()
				elements.append(new_feature)
				relations[ new_feature['id'] ] = new_feature

			for member in new_feature['members']:
				ways[ member['ref'] ]['parents'].add(new_feature['id'])

			fix_member_order(new_feature)  # Update member and coordinate attributes

			if "coordinates" not in new_feature:
				message ("\t*** Split not complete for relation %i\n" % relation_id)
			else:
				features.append(new_feature)
				new_feature['area'] = abs(multipolygon_area(new_feature['coordinates']))
				min_bbox, max_bbox = get_bbox(new_feature['coordinates'][0])  # Outer
				new_feature['min_bbox'] = min_bbox
				new_feature['max_bbox'] = max_bbox

			if new_feature['topo'] == set(["wood"]):
				check_grid(new_feature)

			count_split_new += 1

		if old_relation['topo'] == set(["wood"]):
			check_grid(old_relation)

		count_split += 1

		# Check unused elements

		if inner_members:
			message ("\t*** Remaining inner members after splitting relation %i:\n\t\t%s\n" % (relation_id, str(inner_members)))

		for way_id in split_relation_members:
			if "FIXME" in ways[ way_id ]['tags'] and ways[ way_id ]['tags']['FIXME'] == "Split":
				message ("\t*** Split of relation %s failed for way %s\n" % (relation_id, ways[ way_id ]['id']))

	message ("\tSplit %i relations into %i new relations\n" % (count_split, count_split_new))

	# Step 2: Merge
	# Merge relations which are identified by FIXME=Merge on common member.

	updated_relations = []
	removed_relations = []

	for way in ways.values():
		if "FIXME" in way['tags'] and way['tags']['FIXME'] in ["Merge", "Join"] and "action" in way and way['action'] == "modify":

			# Check if merge is permitted

			parents = list(way['parents'])
			if len(parents) != 2:
				message ("\t*** Exactly 2 parents not found for merging way %i\n" % way['id'])
				way['tags']['NO_MERGE'] = "2 parents not found"
				continue

			relation1 = copy.deepcopy(relations[ parents[0] ])  # Copy for potential roll-back
			relation2 = copy.deepcopy(relations[ parents[1] ])

			if relation1['incomplete'] or "coordinates" not in relation1:  # area
				message ("\t*** Incomplete or unclosed merging relation %i\n" % relation1['id'])
				way['tags']['NO_MERGE'] = "Incomplete or unclosed relation"
				continue
			if relation2['incomplete'] or "coordinates" not in relation2:  # area
				message ("\t*** Incomplete or unclosed merging relation %i\n" % relation2['id'])
				way['tags']['NO_MERGE'] = "Incomplete or unclosed relation"
				continue
			if relation1['topo'] != relation2['topo']:
				message ("\t*** Relations %i and %i not same topo type\n" % (relation1['id'], relation2['id']))
				way['tags']['NO_MERGE'] = "Not same topo type"

			# Keep largest existing area, based on original area size before merging (area updated at the end)

			if relation1['area'] < relation2['area'] and relation2['id'] > 0:
				relation1, relation2 = relation2, relation1

			# Merge relation2 into relation1

			relation2_members = [ member2['ref'] for member2 in relation2['members'] ]
			removed_members = []

			for member1 in relation1['members'][:]:
				if member1['ref'] in relation2_members:
					relation1['members'].remove(member1)  # Remove all common members (regardless of FIXME tag)
					removed_members.append(member1['ref'])

			for member2 in relation2['members'][:]:
				if member2['ref'] not in removed_members:
					relation1['members'].append(member2)  # Merge into relation1
					ways[ member2['ref'] ]['parents'].add(relation1['id'])
					ways[ member2['ref'] ]['parents'].remove(relation2['id'])

			if "coordinates" not in relation1:
				message ("Missing coordinates: %s\n" % str(relation1))
			del relation1['coordinates']
			fix_member_order(relation1)

			if "coordinates" not in relation1:
				message ("\t*** Could not merge relations #%i and #%i\n" % (relation1['id'], relation2['id']))
				relation1['tags']['NO_MERGE'] = "Could not merge #" + str(relation2['id'])
				continue

			# Check if former outer members now are inner

			patches = []
			for i, patch in enumerate(relation1['member_patches']):
				patch_record = {
					'members': patch,
					'coordinates': relation1['coordinates'][i],
					'area': abs(polygon_area(relation1['coordinates'][i]))
				} 
				patches.append(patch_record)

			patches.sort(key=lambda patch: patch['area'], reverse=True)  # Largest/outer polygon first

			relation1['coordinates'] = [ patch['coordinates'] for patch in patches ]
			relation1['member_patches'] = [ patch['members'] for patch in patches ]
			relation1['members'] = [ member for patch in patches for member in patch['members'] ]  # Flat, ordered member list

			for patch in relation1['member_patches'][1:]:
				for member in patch:
					if member['role'] == "outer":
						member['role'] = "inner"  # Swap role - outer becomes inner

			# Update settings for surviving relation

			if "MERGED" in relation1['tags']:
				del relation1['tags']['MERGED']

			merge_tags(relation1, relation2['tags'])  # Update member and coordinate attributes

			relation1['tags']['MERGED'] = str(relation2['id'])
			relation1['action'] = "modify"
			updated_relations.append(relation1)  # Update area at the end

			# Update settings for obsolete relation

			for member_ref in removed_members:
				member_way = ways[ member_ref ]
				member_way['parents'].remove(relation1['id'])
				member_way['parents'].remove(relation2['id'])
				if "FIXME" in member_way['tags'] and member_way['tags']['FIXME'] in ["Merge", "Join"]:
					del member_way['tags']['FIXME']
				else:
					member_way['tags']['NO_FIXME'] = "Merged without FIXME=Merge"  # Common member did not have FIXME tag
				if not member_way['parents']:
					delete_way(member_way)

			relation2['action'] = "delete"
			relation2['members'] = []
			relation2['incomplete'] = True
			if relation2['id'] < 0:
				removed_relations.append(relation2)

			relations[ relation1['id'] ].update(relation1)
			relations[ relation2['id'] ].update(relation2)
			count_merge += 1

	# Update area and bbox

	for relation in updated_relations:
		area = abs(multipolygon_area(relation['coordinates']))
		relation['area'] = area

		min_bbox, max_bbox = get_bbox(relation['coordinates'][0])  # Outer
		relation['min_bbox'] = min_bbox
		relation['max_bbox'] = max_bbox

		if relation['topo'] == set(("wood")):
			check_grid(relation)

	# Delete new unused relations (only new/negative id's were selected)

	for relation in removed_relations[:]:
		features.remove(relation)
		del relations[ relation['id'] ]
		elements.remove(relation)

	message ("\tMerged %i relations\n" % count_merge)



# Combine wood grid lines

def combine_grid_lines():

	# Identify potential candidates for combinations

	grid_ways = []
	for way in ways.values():
		if "grid" in way and not way['incomplete']:
			grid_ways.append(way)

	count_grid = 0
	count_simplify = 0

	# Loop ways and combine where possible

	for way1 in grid_ways:
		if not way1['incomplete']:  # May be removed during iterations
			for end in [0, -1]:
				joint_node = nodes[ way1['nodes'][ end ] ]
				for way_id2 in list(joint_node['parents']):
					way2 = ways[ way_id2 ]

					if (way2['id'] != way1['id']
							and way2 in grid_ways
							and way1['grid'] == way2['grid']
							and way1['parents'] == way2['parents']
							and not way2['incomplete']
							and not any(relations[ relation_id ]['incomplete'] or "grid" not in relations[ relation_id ] for relation_id in way2['parents'])):

						# Combine into one way

						new_nodes = [ way1['nodes'][ abs(end) - 1 ] ]
						if way2['nodes'][0] == joint_node['id']:
							new_nodes.append(way2['nodes'][-1])
						else:
							new_nodes.append(way2['nodes'][0])

						# Update nodes

						nodes[ new_nodes[-1] ]['parents'].add(way1['id'])
						joint_node['parents'].remove(way1['id'])

						for node_id in way1['nodes'][1:-1]:
							nodes[ node_id ]['parents'].remove(way1['id'])
							if not nodes[ node_id ]['parents']:
								nodes[ node_id ]['action'] = "delete"

						way1['nodes'] = new_nodes
						way1['coordinates'] = [ [ ( nodes[ node_id ]['lon'], nodes[ node_id ]['lat'] ) for node_id in new_nodes ] ]
						way1['tags']['GRID'] = "combine"
						way1['action'] = "modify"

						# Remove way2 from relations

						for relation_id in way2['parents']:
							relation = relations[ relation_id ]

							for member in relation['members']:
								if member['ref'] == way2['id']:
									relation['members'].remove(member)

							if "member_patches" in relation:
								for patch in relation['member_patches']:
									for member in patch[:]:
										if member['ref'] == way2['id']:
											patch.remove(member)

							relation['action'] = "modify"

						delete_way(way2)
						count_grid += 1

			# Simplify to two nodes for grid lines

			if len(way1['nodes']) > 2 and line_length(way1['coordinates'][0]) > 15:
				for node_id in way1['nodes'][1:-1]:
					node = nodes[ node_id ]
					node['parents'].remove(way1['id'])
					if not node['parents']:
						node['action'] = "delete"

				way1['nodes'] = [ way1['nodes'][0], way1['nodes'][-1] ]
				way1['coordinates'] = [ [ way1['coordinates'][0][0], way1['coordinates'][0][-1] ] ]
				way1['tags']['GRID'] = "simplify"
				way1['action'] = "modify"
				count_simplify += 1

	if count_grid > 0:
		message ("\tCombined %i wood grid lines and simplified %i\n" % (count_grid, count_simplify))



# Hide administrative boundary objects to avoid snapping to their nodes by hiding their nodes.
# To be run last, before output.

def remove_admin_boundary():

	message ("\tIdentify boundary=* elements to hide ...\n")

	boundary_ways = set()  # Will contain ways which define a boundary=*

	# Add members of relations tagged with boundary=*
	for relation in relations.values():
		if "boundary" in relation['tags'] or "was:boundary" in relation['tags']:
			for member in relation['members']:
				if member['ref'] in ways:
					boundary_ways.add(ways[ member['ref'] ])

	# Add ways tagged with boundary=*
	for way in ways.values():
		if "boundary" in way['tags'] or "was:boundary" in way['tags']:
			boundary_ways.add(way)

	# Hide nodes belonging to ways tagged with boundary=*
	count_node = 0
	for node in nodes.values():
		if (node['parents']
				and all(parent in ways and ("boundary" in ways[ parent ]['tags'] or "was:boundary" in ways[ parent ]['tags'])
						for parent in node['parents'])):
			node['hide'] = True
			count_node += 1

	# Hide ways where all nodes are now hidden
	count_way = 0
	for way in boundary_ways:
		has_node = False
		for node_id in way['nodes']:
			if node_id in nodes:
				node = nodes[ node_id ]
				if ("used" in node
						or any(parent not in ways or ("boundary" not in ways[ parent ]['tags'] and "was:boundary" not in ways[ parent ]['tags'])
								for parent in node['parents'])):
					has_node = True
		if not way['incomplete'] and not has_node:
			way['hide'] = True
			count_way += 1

	message ("\t\tHide %i boundary nodes, %i ways\n" % (count_node, count_way))



# Identify islands, will get name later

def create_islands():


	# Internal function for connecting coastlines and shores

	def connect_coastline(coastlines):

		nonlocal count_old, count_new

		# Connect coastlines until exhausted

		while coastlines:

			# Build closed ring if possible

			combination = coastlines.pop(0)
			combination_nodes = combination['nodes']
			combination_coordinates = combination['coordinates'][0]
			combination_ways = [ combination ]

			found = True
			while found and combination_coordinates[0] != combination_coordinates[-1]:
				found = False
				for coastline in coastlines[:]:
					if coastline['coordinates'][0][0] == combination_coordinates[-1]:
						combination_coordinates = combination_coordinates + coastline['coordinates'][0][1:]
						combination_nodes = combination_nodes + coastline['nodes'][1:]
						found = True
					elif coastline['coordinates'][0][-1] == combination_coordinates[-1]:
						combination_coordinates = coastline['coordinates'][0] + list(reversed(combination_coordinates))[1:]
						combination_nodes = coastline['nodes'] + list(reversed(combination_nodes))[1:]
						found = True

					if found:
						combination_ways.append(coastline)
						coastlines.remove(coastline)
						break

			# Create/tag island if closed ring

			if combination_coordinates[0] == combination_coordinates[-1]:

				# First avoid outer perimeter of lake/river being selected

				area = abs(polygon_area(combination_coordinates))
				all_parents = set()
				for way in combination_ways:
					for parent_id in way['parents']:
						if relations[ parent_id ]['topo'] & set(["water", "river"]):
							all_parents.add(parent_id)
				area_parents = sum(abs(polygon_area(relations[ parent_id ]['coordinates'][0])) for parent_id in all_parents)
				if all_parents and area + 5 > area_parents:
					continue

				# Tag according to area

				if area >= island_size:
					tags = { 'place': 'island' }
				else:
					tags = { 'place': 'islet' }

				# Check if parent relation(s) already exist

				common_parents = set.intersection(*[ way['parents'] for way in combination_ways ])
				found_island = None
				found_relation = None
				for parent_id in common_parents:
					parent = relations[ parent_id ]
					if "island" in parent['topo']:
						found_island = parent
					if not "place" in parent['tags']:
						found_relation = parent

				if found_island is not None:  # Island already tagged
					merge_tags(found_island, tags)
					count_old += 1

				elif found_relation is not None:  # Relation found without place=* tag
					merge_tags(found_relation, tags)
					found_relation['topo'].add("island")
					count_new += 1

				else:
					# create new relation

					members = []
					for way in combination_ways:
						member = {
							'type': 'way',
							'ref': way['id'],
							'role': 'outer'
						}
						members.append(member)

					tags['type'] = "multipolygon"

					relation = {
						'type': 'relation',
						'id': new_id(),
						'members': members,
						'tags': tags,
						'coordinates': [ combination_coordinates ],
						'member_patches': [ members ],
						'topo': set(["island"]),
						'area': area,
						'incomplete': False
					}
					elements.append(relation)
					relations[ relation['id'] ] = relation
					features.append(relation)
					count_new += 1

					for member in members:
						ways[ member['ref'] ]['parents'].add(relation['id'])


	# Start of main function

	message ("Identify islands ...\n")
	count_old = 0
	count_new = 0

	# Part 1: Identify inner rings in lakes

	for lake in features:
		if "water" in lake['topo'] or "river" in lake['topo']:
			if "member_patches" in lake and len(lake['member_patches']) > 1:

				# All inner patches of lakes are islands

				for i, inner_patch in enumerate(lake['member_patches'][1:], 1):

					# Determine island/islet tag

					area = abs(polygon_area(lake['coordinates'][i]))
					if area >= island_size:
						tags = { 'place': 'island' }
					else:
						tags = { 'place': 'islet' }

					# Either, 1) closed way is island if it is inner member of water relation

					if len(inner_patch) == 1:
						way = ways[ inner_patch[0]['ref'] ]
						if "intermittent" not in way['tags']:
							if "island" in way['topo']:
								count_old += 1
							else:
								count_new += 1
							way['topo'].add("island")
							merge_tags(way, tags)

					# Or, 2) inner patch is multiple members, so establish relation

					else:
						# Get members

						parents = [ ways[ member['ref'] ]['parents'] for member in inner_patch ]
						common_parents = set.intersection(*parents) - set([ lake['id'] ])
						if len(common_parents) >= 1:
							relation = relations[ list(common_parents)[0] ]

						# Use existing relation if it already exists (typically wood)

						if len(common_parents) >= 1 and "topo" in relation and len(relation['members']) == len(inner_patch):
							if "intermittent" not in relation['tags']:
								if "island" in relation['topo']:
									count_old += 1
								else:
									count_new += 1								
								relation['topo'].add("island")
								merge_tags(relation, tags)

						# Or create new relation for island

						else:
							members = copy.deepcopy(inner_patch)
							for member in members:
								member['role'] = "outer"
							tags['type'] = "multipolygon"

							relation = {
								'type': 'relation',
								'id': new_id(),
								'members': members,
								'tags': tags,
								'coordinates': [ lake['coordinates'][i] ],
								'member_patches': [ members ],
								'topo': set(["island"]),
								'area': area,
								'incomplete': False
							}
							elements.append(relation)
							relations[ relation['id'] ] = relation
							features.append(relation)
							count_new += 1

							for member in members:
								ways[ member['ref'] ]['parents'].add(relation['id'])


	# Part 2: Identify connected coastlines

	# Identify closed coastline ways + build list of candidates

	coastlines = []
	for coastline in ways.values():
		if "coastline" in coastline['topo'] and not coastline['incomplete']:

			# Check if way is circular
			if coastline['nodes'][0] == coastline['nodes'][-1]:
				if len(coastline['nodes']) > 2:
					area = abs(polygon_area(coastline['coordinates'][0]))
					if area >= island_size:
						tags = { 'place': 'island' }
					else:
						tags = { 'place': 'islet' }
					merge_tags(coastline, tags)
					if "island" in coastline['topo']:
						count_old += 1
					else:
						coastline['topo'].add("island")
						count_new += 1
			else:
				coastlines.append(coastline)  # Build list of candidates

	connect_coastline(coastlines)


	# Part 3: Identify islands across river, lakes and coastlines

	shores = []

	# Add unused coastline segments
	for shore in ways.values():
		if ("coastline" in shore['topo']
				and "island" not in shore['topo']
				and not shore['incomplete']
				and not any(relations[ parent ]['topo'] & set(["island", "river", "water"]) for parent in shore['parents'] if parent in relations)):
			shores.append(shore)

	# Add outer members of lakes and rivers if connected with another lake or river
	for lake in features:
		if "water" in lake['topo'] or "river" in lake['topo']:
			if "member_patches" in lake and lake['member_patches']:
				found_connection = False
				lake_shores = []
				for member in lake['member_patches'][0]:
					if member['ref'] in ways and not ways[ member['ref'] ]['incomplete']:
						shore = ways[ member['ref'] ]
						if not any(relations[ parent ]['topo'] & set(["river", "water", "coastline"])
									for parent in shore['parents'] if parent in relations and parent != lake['id']):
							lake_shores.append(shore)
						else:
							found_connection = True

				if found_connection:
					shores.extend(lake_shores)

	connect_coastline(shores)

	message ("\tFound %i existing tagged islands and created %i new\n" % (count_old, count_new))



# Fix various tagging issues for lakes and rivers

def fix_water_tags():

	message ("Fix water tagging...\n")
	count = 0

	for feature in features:
		if "water" in feature['topo']:

			# Fix minimum reservoir elecation from earlier import
			if "LRV" in feature['tags']:
				merge_tags (feature, { 'ele:min': feature['tags'].pop("LRV", None) })
				merge_tags (feature, { 'water': 'reservoir' })
				count += 1

			# Add water=lake for largest lakes
			if not ("water" in feature['tags'] and feature['tags']['water'] == "reservoir"):
				if feature['area'] > min_lake_size:
					merge_tags(feature, { 'water': 'lake' })
					count += 1
				elif feature['area'] < 0.1 * min_lake_size and "water" in feature['tags'] and feature['tags']['water'] == "lake":
					del feature['tags']['water']
					feature['tags']['OSM_water'] = "lake"
					feature['action'] = "modify"
					count += 1

			# Remove superfluous tags (likely from iD)
			for tag in ["tidal", "salt"]:
				if tag in feature['tags'] and feature['tags'][ tag ] == "no":
					merge_tags(feature, { 'OSM_' + tag : feature['tags'].pop(tag, None) })

		if "river" in feature['topo']:

			# Deprecate waterway=riverbank if possible
			if "waterway" in feature['tags'] and feature['tags']['waterway'] == "rivrbank" and "natural" not in feature['tags']:
				feature['tags']['natural'] = "water"
				feature['tags']['water'] = "river"
				del feature['tags']['waterway']
				feature['action'] = "modify"
				count += 1

		if "island" in feature['topo']:

			# Deprecate island=yes
			if "island" in feature['tags'] and feature['tags']['island'] == "yes":
				del feature['tags']['island']
				feature['action'] = "modify"
				count += 1

	message ("\tModified %s water tags\n" % count)



# Get name from NVE Innsjødatabasen
# API reference: https://nve.geodataonline.no/arcgis/rest/services/Innsjodatabase2/MapServer

def get_nve_lakes():

	message ("Load lake and reservoir data from NVE...\n")

	# Step 1: Load reservoirs from NVE to get revervoir ref

	reservoirs = {}
	load_count = 0  # Paged index
	more = True

	while more:
		query = ("where=1=1&outFields=magasinNr,lavesteRegulerteVannstand_moh,hoyesteRegulerteVannstand_moh,naturligVannstand_moh,status"
				"&returnGeometry=false&resultOffset=%i&resultRecordCount=1000&f=json"
					% (load_count))
		url = "https://nve.geodataonline.no/arcgis/rest/services/Vannkraft1/MapServer/6/query?" + query

		request = urllib.request.Request(url, headers=header)
		try:
			file = urllib.request.urlopen(request)
		except urllib.error.HTTPError as err:
			message("\t\t*** %s\n" % err)
			more = False
			continue

		lake_data = json.load(file)
		file.close()

		for feature in lake_data['features']:
			reservoirs [ feature['attributes']['magasinNr' ] ] = feature['attributes']

		load_count += len(lake_data['features'])
		if 'exceededTransferLimit' not in lake_data:
			more = False

	message ("\tLoaded %i reservoirs for Norway\n" % load_count)

	# Step 2: Load lake data from NVE

	lakes = []
	geojson_features = []
	load_count = 0  # Paged index
	more = True

	while more:
		query = ("where=kommNr='%s'&outFields=vatnLnr,navn,hoyde,areal_km2,magasinNr&returnGeometry=true&outSR=4326&geometryPrecision=6&resultOffset=%i&resultRecordCount=1000&f=json"
					% (municipality_id, load_count))
		url = "https://nve.geodataonline.no/arcgis/rest/services/Innsjodatabase2/MapServer/5/query?" + query

		request = urllib.request.Request(url, headers=header)
		try:
			file = urllib.request.urlopen(request)
		except urllib.error.HTTPError as err:
			message("\t\t*** %s\n" % err)
			more = False
			continue

		lake_data = json.load(file)
		file.close()

		for feature in lake_data['features']:

			coordinates = [ (node[0], node[1]) for node in feature['geometry']['rings'][0] ]
			coordinates = simplify_line(coordinates, 1)
			min_bbox, max_bbox = get_bbox(coordinates)

			info = feature['attributes']
			if info['magasinNr'] is not None and info['magasinNr'] in reservoirs:
				lake.update(reservoirs[ info['magasinNr'] ])

			lake = {
				'name': info['navn'],
				'ref:nve:vann': info['vatnLnr'],
				'ref:nve:magasin': info['magasinNr'],
				'area': abs(int(multipolygon_area(feature['geometry']['rings']))),
				'coordinates': coordinates,
				'min_bbox': min_bbox,
				'max_bbox': max_bbox
			}
			if info['hoyde'] is not None:
				lake['ele'] = int(info['hoyde'])
			if info['magasinNr'] is not None and info['magasinNr'] in reservoirs and reservoirs[ info['magasinNr'] ]['lavesteRegulerteVannstand_moh'] is not None:
				lake['ele:min'] = int(reservoirs[ info['magasinNr'] ]['lavesteRegulerteVannstand_moh'])

			lakes.append(lake)

			# Create geojson for output to file

			for tag in list(info.keys()):
				if info[ tag ] is None or not info[ tag ]:
					del info[ tag ]

			geojson_feature = {
				'type': 'Feature',
				'geometry': {
					'type': 'Polygon',
					'coordinates': feature['geometry']['rings']
				},
				'properties': info,
			}
			geojson_feature['properties']['natural'] = "water"
			if "navn" in info:
				geojson_feature['properties']['name'] = info['navn']
			geojson_features.append(geojson_feature)

		load_count += len(lake_data['features'])

		if 'exceededTransferLimit' not in lake_data:
			more = False

	message ("\tLoaded %i NVE lakes\n" % len(lakes))

	# Step 3: Save NVE lakes as geojson

	if nve_output:
		collection = {
			'type': 'FeatureCollection',
			'features': geojson_features
		}

		filename = "nve_vann.geojson"
		file = open(filename, "w")
		json.dump(collection, file)
		file.close()

		message ("\tSaved %i lakes to '%s'\n" % (len(geojson_features), filename))


	# Step 4: Match lakes and update lake info

	lap_time = time.time()
	message ("\tMatching lakes ...\n")

	min_area = 0.5 * min([ lake['area'] for lake in lakes ])

	osm_lakes = []
	for osm_lake in features:
		if "water" in osm_lake['topo'] and osm_lake['area'] > min_area:
			osm_lakes.append(osm_lake)

	count = 0
	display_limit = 1000

	i = len(lakes) + 1
	for nve_lake in lakes:

		i -= 1
		message ("\r\t%i " % i)
		if len(nve_lake['coordinates']) > display_limit and nve_lake['name']:
			message (nve_lake['name'] + " ")

		tags = {}
		for tag in ["ele", "ele:min", "ref:nve:vann", "ref:nve:magasin"]:
			if tag in nve_lake and nve_lake[ tag ] is not None and nve_lake[ tag ]:
				tags[ tag ] = str(nve_lake[ tag ])
		if "ref:nve:magasin" in tags:
			tags['water'] = "reservoir"

		best_hits = 0

		for osm_lake in osm_lakes:
			if (0.5 < abs(nve_lake['area'] / osm_lake['area']) < 1.5
					and nve_lake['min_bbox'][0] < osm_lake['max_bbox'][0] and nve_lake['max_bbox'][0] > osm_lake['min_bbox'][0]
					and nve_lake['min_bbox'][1] < osm_lake['max_bbox'][1] and nve_lake['max_bbox'][1] > osm_lake['min_bbox'][1]):

				hausdorff, hits = hausdorff_distance(nve_lake['coordinates'], osm_lake['coordinates'][0], limit=50, percent=True, polygon=True)

				if hits > best_hits:
					best_hits = hits
					best_lake = osm_lake
					best_hausdorff = hausdorff

		# March if 50% of NVE nodes have hits within 50 meters

		if best_hits > 50:
			merge_tags(best_lake, tags)
			if nve_lake['name'] is not None and nve_lake['name']:
				best_lake['nve_name'] = nve_lake['name']

			osm_lakes.remove(best_lake)
			count += 1

		# Create single node with info if no hit

		else:
			tags['FIXME'] = "Insert NVE lake ref"
			if nve_lake['name'] is not None and nve_lake['name']:
				tags['name'] = nve_lake['name']
			point = polygon_centroid(nve_lake['coordinates'])
			create_point(point, tags)

		if len(nve_lake['coordinates']) > display_limit:
			message ("\r\t%s\r" % (" "*30))

	message ("\r\tMatched %i OSM lakes and created %i nodes for non-matched lakes\n" % (count, len(lakes) - count))
	message ("\tRun time %i seconds\n" % (time.time() - lap_time))



# Split rivers at junctions.
# Many will be recombined later.

def split_streams():

	message ("Split streams at junctions ...\n")

	count_split_rivers = 0
	count_new_segments = 0

	for river in list(ways.values()):
		if "stream" in river['topo'] and not river['parents'] and not river['incomplete'] and "name" not in river['tags']:
			segments = []
			last_node_index = 0

			for i, node_id in enumerate(river['nodes'][1:-1], start=1):
				node = nodes[ node_id ]
				for parent_id in node['parents']:
					if parent_id in ways and not ways[ parent_id ]['incomplete'] and "stream" in ways[ parent_id ]['topo'] and parent_id != river['id']:

						segment = {
							'nodes': river['nodes'][ last_node_index : i + 1],
							'coordinates': river['coordinates'][0][ last_node_index : i + 1]
						}
						segments.append(segment)
						last_node_index = i
						break

			if segments:

				segment = {
					'nodes': river['nodes'][ last_node_index : ],
					'coordinates': river['coordinates'][0][ last_node_index : ]
				}
				segments.append(segment)

				segments.sort(key=lambda river: len(river['nodes']), reverse=True)  # Longest segment first

				for node_id in river['nodes']:
					if river['id'] in nodes[ node_id ]['parents']:
						nodes[ node_id ]['parents'].remove(river['id'])

				river['nodes'] = segments[0]['nodes']
				river['coordinates'] = [ segments[0]['coordinates'] ]
				river['action'] = 'modify'

				for node_id in river['nodes']:
					nodes[ node_id ]['parents'].add(river['id'])				

				for segment in segments[1:]:
					new_river = {
						'type': 'way',
						'id': new_id(),
						'tags': river['tags'].copy(),
						'nodes': segment['nodes'],
						'coordinates': [ segment['coordinates'] ],
						'parents': set(),
						'topo': set(["stream"]),
						'incomplete': False,
						'action': 'modify'
					}
					elements.append(new_river),
					ways[ new_river['id'] ] = new_river
					count_new_segments += 1

					for node_id in new_river['nodes']:
						nodes[ node_id ]['parents'].add(new_river['id'])						

				count_new_segments += 1
				count_split_rivers += 1

	message ("\t%i rivers/streams split into %i segments\n" % (count_split_rivers, count_new_segments))



def get_nve_streams(add_all_centerlines=False, add_short_connections=False, nve_output_only=False):

	# Internal function to check if node is a three-way river junction

	def river_junction(node_id):

		node = nodes[ node_id ]
		if len(node['parents']) < 3:
			return False
		else:
			count = 0
			for parent in node['parents']:
				if parent in ways and "waterway" in ways[ parent ]['tags'] and ways[ parent ]['tags']['waterway'] in ["river", "canal"]:
					count += 1
			if count > 2:
				message ("3-way junction: %s\n" % node_id)
				return True
			else:
				return False


	message ("Load river data from NVE...\n")

	# Pass 1: Load rivers from NVE

	lap = time.time()

	# Get municipality bbox for NVE query

	bbox_min, bbox_max = coordinate_offset(municipality_bbox[0], -1000), coordinate_offset(municipality_bbox[1], 1000)
	bbox_string = urllib.parse.quote("%f,%f,%f,%f" % (bbox_min[0], bbox_min[1], bbox_max[0], bbox_max[1]))

	# Load rivers (paged)

	nve_rivers = []  # Geojson features for output of all rivers inside bbox
	nve_river_count = 0
	more_rivers = True

	while more_rivers:
		query = "where=1=1&geometryType=esriGeometryEnvelope&geometry=%s&inSR=4326&outFields=*&returnGeometry=true&resultOffset=%i&resultRecordCount=1000&f=json&outSR=4326&geometryPrecision=6" \
					% (bbox_string, nve_river_count)   
		url = "https://nve.geodataonline.no/arcgis/rest/services/Elvenett1/MapServer/2/query?" + query

		request = urllib.request.Request(url, headers=header)
		try:
			file = urllib.request.urlopen(request)
		except urllib.error.HTTPError as err:
			message("\t\t*** %s\n" % err)
			more_rivers = False
			continue

		river_data = json.load(file)  # Paging results (default 1000 rivers)
		file.close()

		# Loop river segments and store

		for river in river_data['features']:
			# Add OSM tags
			if river['attributes']['objektType'] not in ["InnsjøMidtlinje", "InnsjøMidtlinjeReg", "ElvelinjeFiktiv"]:
				if "elvenavn" in river['attributes'] and river['attributes']['elvenavn'] and river['attributes']['elvenavn'].strip():
					river['attributes']['waterway'] = "river"  # Main rivers. Alternative identification: vnrNfelt ends with Z (from Regine).
					river['attributes']['name'] = river['attributes']['elvenavn']
				else:
					river['attributes']['waterway'] = "stream"  # Mostly smaller branching stream

			coordinates = [ ( point[0], point[1] ) for point in river['geometry']['paths'][0] ]  # Get tuples
			for path in river['geometry']['paths'][1:]:
				path_coordinates = [ ( point[0], point[1] ) for point in path ]
				if path_coordinates[0] == coordinates[-1]:
					coordinates.extend(path_coordinates[1:])
					message ("*** Path match 1\n")
				elif path_coordinates[-1] == coordinates[0]:
					coordinates = path_coordinates + coordinates[1:]
					message ("*** Path match 2\n")
				else:
					message ("*** No path match\n")
			river['geometry']['paths'] = coordinates
			river['min_bbox'], river['max_bbox'] = get_bbox(coordinates)
			nve_rivers.append(river)

		nve_river_count += len(river_data['features'])
		message ("\r\t%i " % nve_river_count)

		if 'exceededTransferLimit' not in river_data:
			more_rivers = False

	message ("\r\tLoaded %i river/stream segments in bounding box from NVE\n" % nve_river_count)


	# Pass 2: Output Elvis geojson

	if nve_output or nve_output_only:
		nve_features = []
		for river in nve_rivers:
			if nve_output_only or debug:
				properties = river['attributes']
			else:
				properties = {
					'OBJEKT': river['attributes']['objektType'],
					'ELVID': river['attributes']['elvId'],
					'STRAHLER': river['attributes']['elveordenStrahler'],
					'VASSDRAG': river['attributes']['vassdragsNr']
				}
				for tag in ["waterway", "name", "BOUNDARY"]:
					if tag in river['attributes']:
						properties[ tag ] = river['attributes'][ tag ]

			feature = {
				'type': 'Feature',
				'properties': properties,
				'geometry': {
					'type': 'LineString',
					'coordinates': river['geometry']['paths']
				}
			}
			nve_features.append(feature)

		feature_collection = {
			'type': 'FeatureCollection',
			'features': nve_features
		}

		filename = "elvis.geojson"
		file = open(filename, "w")
		json.dump(feature_collection, file, indent=2, ensure_ascii=False)
		file.close()
		message ("\tSaved %i NVE rivers and streams to '%s'\n" % (nve_river_count, filename))

	if nve_output_only:  # No further actions if geojson output only
		return

	# Get bbox for OSM rivers

	for river in ways.values():
		if "stream" in river['topo']:
			[ river['min_bbox'], river['max_bbox'] ] = get_bbox(river['coordinates'][0])


	# Pass 3: Identify river centerlines for riverbanks + within municipality

	if add_centerlines:

		if add_all_centerlines:
			message ("\tIdentify all river centerlines ... ")
		else:
			message ("\tIdentify missing river centerlines ... ")

		load_municipality_boundary()

		# Build list of riverbanks from OSM
		osm_riverbanks = []
		for feature in features:
			if "river" in feature['topo'] and not feature['incomplete']:
				osm_riverbanks.append(feature)

		# Build list of OSM rivers
		osm_rivers = []
		for way in ways.values():
			if "stream" in way['topo'] and not way['incomplete']:
				osm_rivers.append(way)

		count_load = 0
		new_nodes = {}

		for river in nve_rivers:

			# Keep for riverbanks only
			if river['attributes']['objektType'] != "ElvBekkMidtlinje":
				continue

			if not add_short_connections and river['attributes']['waterway'] == "stream":
				continue

			coordinates = river['geometry']['paths']
			way_nodes = [None] * len(coordinates)

			# Match with OSM riverbanks (avoid rivers outside of municipality boundary)

			inside = False
			for riverbank in osm_riverbanks:
				if (river['min_bbox'][0] <= riverbank['max_bbox'][0] and river['max_bbox'][0] >= riverbank['min_bbox'][0]
						and river['min_bbox'][1] <= riverbank['max_bbox'][1] and river['max_bbox'][1] >= riverbank['min_bbox'][1]):

					# Check if inside municipality
					for point in coordinates:
						if inside_multipolygon(point, municipality_border):
							inside = True
							break

					if not inside:
						if close_to_border(coordinates, 100):
							inside = True

					# Check if NVE centerline is matching OSM river
					if inside and not add_all_centerlines:

						for river2 in osm_rivers:
							if (river['min_bbox'][0] <= river2['max_bbox'][0] and river['max_bbox'][0] >= river2['min_bbox'][0]
									and river['min_bbox'][1] <= river2['max_bbox'][1] and river['max_bbox'][1] >= river2['min_bbox'][1]):

								hits = hausdorff_distance(coordinates, river2['coordinates'][0], limit=10, hits=True)
								if len(hits) > 0.6 * len(coordinates):
									inside = False  # Do not add NVE centerline
									break

					# Adjust end points slightly to match river polygon
					if inside:
						if riverbank['type'] == "way":
							members = [ riverbank['id'] ]
						else:
							members = [ member['ref'] for member in riverbank['member_patches'][0] ]  # Outer

						for end in [ 0, -1 ]:
							for way_id in members:
								way = ways[ way_id ]
								for node_id in way['nodes'][1:]:
									node = nodes[ node_id ]
									point = ( node['lon'], node['lat'] )
									if distance(point, coordinates[ end ]) < 0.1:  # Meters
										coordinates[ end ] = point
										way_nodes[ end ] = node_id
										break

			if inside:
				element = {
					'type': 'way',
					'id': new_id(),
					'nodes': way_nodes,
					'tags': {
						'waterway': river['attributes']['waterway']
					},
					'action': 'modify',
					'parents': set(),
					'coordinates': [ coordinates ],
					'incomplete': False,
					'topo': set(["stream"]),
					'min_bbox': river['min_bbox'],
					'max_bbox': river['max_bbox'],
					'elvis': river['attributes']['elvId'] + "*",  # Identification of elvis source + river branch id
					'direction': "Elvis"
				}

				if "name" in river['attributes']:
					element['tags']['ELVIS'] = river['attributes']['name']
				if element['tags']['waterway'] == "river":
					element['tags']['FIXME'] = "Swap river centerline"
					count_load += 1
				else:
					element['tags']['FIXME'] = "Connect to stream"

				# Create nodes
				for i, point in enumerate(coordinates):
					if way_nodes[i] is None:
						if point in new_nodes:
							way_nodes[i] = new_nodes[ point ]
							nodes[ way_nodes[i] ]['parents'].add(element['id'])
						else:
							way_nodes[i] = create_point(point, {})
							new_nodes[ point ] = way_nodes[i]
					nodes[ way_nodes[i] ]['parents'].add(element['id'])

				elements.append(element)
				ways[ element['id'] ] = element

		message ("%i NVE river centerline segments inserted for %i riverbanks\n" % (count_load, len(osm_riverbanks)))


	# Pass 4: Identify incomplete junctions along municipality boundary

	message ("\tIdentify incomplete connected rivers/streams ... ")

	count_boundary = 0
	for river in ways.values():
		if "stream" in river['topo'] and not river['incomplete']:
			for end in [0, -1]:
				node = nodes[ river['nodes'][ end ] ]
				if len(node['parents']) > 1:
					point = ( node['lon'], node['lat'] )
					for parent_id in node['parents']:
						if (parent_id != river['id'] and parent_id not in ways or ways[ parent_id ]['incomplete']
								and close_to_border([ point ], 5)):
							node['tags']['FIXME'] = "Download " + river['tags']['waterway']
							node['action'] = "modify"
							count_boundary += 1
							break

	message ("Marked %i nodes for downloading\n" % count_boundary)


	# Pass 5: Match to verify stream/river direction + tag main rivers with name

	count_rivers = sum(("stream" in way['topo'] and "elvis" not in way) for way in ways.values())
	message ("\tMatching %i rivers/streams ... " % count_rivers)

	# Select all NVE rivers if stream direction check, or main NVE rivers otherwise
	nve_selection_rivers = []
	for river in nve_rivers:
		if river['attributes']['objektType'] in ["ElvBekk", "ElvBekkMidtlinje"] and (turn_stream or "name" in river['attributes']):
			nve_selection_rivers.append(river)

	count_river = 0
	count_match = 0
	count_reverse = 0
	count_main = 0

	for river1 in ways.values():
		if "stream" in river1['topo'] and "elvis" not in river1:
			count_river += 1
			all_hits = set()
			best_match = None
			best_hits = 0

			for river2 in nve_selection_rivers[:]:
				if (river1['min_bbox'][0] <= river2['max_bbox'][0] and river1['max_bbox'][0] >= river2['min_bbox'][0]
						and river1['min_bbox'][1] <= river2['max_bbox'][1] and river1['max_bbox'][1] >= river2['min_bbox'][1]):

					hits = hausdorff_distance(river1['coordinates'][0], river2['geometry']['paths'], limit=5, hits=True)
					if len(hits) > 1:
						all_hits.update(set(hits))
						if len(hits) > best_hits:
							best_hits = len(hits)
							best_match = river2
						if len(hits) == len(river1['coordinates'][0]):
							break

			if len(all_hits) > 0.6 * len(river1['coordinates'][0]):
				river2 = best_match

				# Turn river if needed. NVE assumed to have correct direction.
				if turn_stream and "direction" not in river1:
					hits_list = sorted(all_hits)
					coordinates2 = river2['geometry']['paths']

					# Check matching node order in NVE river
					turn = False
					d, i1 = shortest_distance(river1['coordinates'][0][0], coordinates2)
					d, i2 = shortest_distance(river1['coordinates'][0][-1], coordinates2)

					if i1 > i2:
						turn = True
					elif i1 == i2:
						# If same node, get closest coordinate on NVE river
						if i1 + 1 == len(river2['geometry']['paths']):
							i1 -= 1
						d, p1 = line_distance(coordinates2[i1], coordinates2[i1 + 1], river1['coordinates'][0][0], get_point=True)
						d, p2 = line_distance(coordinates2[i1], coordinates2[i1 + 1], river1['coordinates'][0][-1], get_point=True)
						if distance(coordinates2[i1], p1) > distance(coordinates2[i1], p2):
							turn = True

					if turn:
						river1['coordinates'][0].reverse()
						river1['nodes'].reverse()
						river1['tags']['REVERSED'] = "Elvis"
						river1['action'] = "modify"
						count_reverse += 1

				if "name" in river2['attributes']:
					river1['tags']['ELVIS'] = river2['attributes']['name']
					river1['elvis'] = river2['attributes']['elvId']
					river1['action'] = "modify"
					count_main += 1

				elif (river2['attributes']['elveordenStrahler'] > 1
						or len(nodes[ river1['nodes'][0] ]['parents']) > 1
						or len(nodes[ river1['nodes'][-1] ]['parents']) == 2):
					river1['elvis'] = river2['attributes']['elvId']

				river1['direction'] = "Elvis"
				count_match += 1

	if count_river > 0:
		message ("%i%% matched\n" % (100 * count_match / count_river))
	else:
		message ("0 matched\n")
	message ("\t%i main rivers identified\n" % count_main)
	message ("\t%i rivers/streams reversed\n" % count_reverse)


	# Pass 6: Combine short stream connections at riverbanks

	if add_short_connections and add_centerlines and combine_streams:
		# Select waterways which have not been matched
		osm_rivers = []
		for river in ways.values():
			if "stream" in river['topo'] and not ("elvis" in river and "*" in river['elvis']):
				osm_rivers.append(river)

		count_combine = 0
		count_orphans = 0

		for river1 in list(ways.values()):
			if "stream" in river1['topo'] and "elvis" in river1 and "*" in river1['elvis']:
				found = False
				for river2 in osm_rivers:

					if river1['coordinates'][0][0] == river2['coordinates'][0][-1] or distance(river1['coordinates'][0][0], river2['coordinates'][0][-1]) < 5:
						river2['coordinates'][0] = river2['coordinates'][0] + river1['coordinates'][0][1:]
						river2['nodes'].extend(river1['nodes'][1:])
						found = True
						break

				if False: #not found:
					best_gap = 5
					best_river = None
					for river2 in osm_rivers:
						gap = distance(river1['coordinates'][0][0], river2['coordinates'][0][-1])
						if gap < best_gap:
							best_gap = gap
							best_river = river2
							found = True

					if found:
						river2 = best_river
						river2['coordinates'][0] = river2['coordinates'][0] + river1['coordinates'][0][1:]
						river2['nodes'].extend(river1['nodes'][1:])

				if found:
					for node_id in river1['nodes']:
						nodes[ node_id ]['parents'].add(river2['id'])
					river2['direction'] = "Elvis"  # Confirmed direction
					delete_way(river1)
					del ways[ river1['id'] ]
					elements.remove(river1)
					osm_rivers.remove(river2)
					count_combine += 1
#					break

				if not found:
					count_orphans += 1

		if count_combine > 0 or count_orphans > 0:
			message ("\t%i short riverbank connections combined, %i not combined\n" % (count_combine, count_orphans))


	# Pass 7: Combine matched NVE river segments into longer ways

	if combine_streams:
		# Selected waterways which have been matched and which are not boundary rivers
		osm_rivers = []
		for river in ways.values():
			if "elvis" in river and "stream" in river['topo'] and not river['parents']:  # and "boundary" not in river['extras']:
				osm_rivers.append(river)

		count_combine = 0
		count_segments = 1

		while osm_rivers:
			combination = osm_rivers.pop(0)
			combination_nodes = combination['nodes']
			combination_coordinates = combination['coordinates'][0]
			combination_rivers = [ combination ]
			combination_tags = combination['tags'].copy()

			found = True
			while found and combination_coordinates[0] != combination_coordinates[-1]:
				found = False
				for river in osm_rivers[:]:
					if (river['elvis'] == combination['elvis']
							and river['tags']['waterway'] == combination_tags['waterway']
							and (("tunnel" in river['tags']) == ("tunnel" in combination_tags))
							and not ("name" in river['tags'] and "name" in combination_tags and combination_tags['name'] != river['tags']['name'])
							and not ("ssr:stedsnr" in river['tags'] and "ssr:stedsnr" in combination_tags and combination_tags['ssr:stedsnr'] != river['tags']['ssr:stedsnr'])
							and not ("FIXME" in river['tags'] and "name" in combination_tags)
							and not ("name" in river['tags'] and "FIXME" in combination_tags)
							and not (river['nodes'][0] in combination_nodes and river['nodes'][-1] in combination_nodes)):  # Avoid circular combination

						if river['coordinates'][0][0] == combination_coordinates[-1]:
							combination_coordinates = combination_coordinates + river['coordinates'][0][1:]
							combination_nodes = combination_nodes + river['nodes'][1:]
							found = True
						elif river['coordinates'][0][-1] == combination_coordinates[0]:
							combination_coordinates = river['coordinates'][0] + combination_coordinates[1:]
							combination_nodes = river['nodes'] + combination_nodes[1:]
							found = True

						if found:
							combination_rivers.append(river)
							osm_rivers.remove(river)
							combination_tags.update(river['tags'])
							break

			if len(combination_rivers) > 1:
				combination_rivers.sort(key=lambda river: len(river['nodes']), reverse=True)  # Longest river survives

				# Get old id, if possible
				combined_river = None
				for river in combination_rivers:
					if river['id'] > 0:
						combined_river = river
						break
				if combined_river is None:
					combined_river = combination_rivers[0]

				combination_rivers.remove(combined_river)
				combined_river['nodes'] = combination_nodes
				combined_river['coordinates'] = [ combination_coordinates ]
				combined_river['action'] = "modify"

				for river in combination_rivers:
					if combined_river['tags']['waterway'] == "river" or river['tags']['waterway'] == "river":
						combined_river['tags']['waterway'] = "river"
					elif combined_river['tags']['waterway'] == "canal" or river['tags']['waterway'] == "canal":
						combined_river['tags']['waterway'] = "canal"							

					# Move nodes to combined river
					for node in river['nodes']:
						if river['id'] in nodes[ node ]['parents']:
							nodes[ node ]['parents'].remove(river['id'])
						nodes[ node ]['parents'].add(combined_river['id'])

					merge_tags(combined_river, river['tags'], overwrite=False)
					delete_way(river)

				count_segments += len(combination_rivers)
				count_combine += 1

		if count_combine > 0:
			message ("\t%i river/stream segments combined into %i\n" % (count_segments, count_combine))


	# Pass 8: Split at riverbanks

	if add_centerlines and add_all_centerlines:
		count_split = 0

		for riverbank in features:
			if "river" not in riverbank['topo'] or riverbank['incomplete'] or riverbank['area'] < 5000:
				continue

			inside = False

			# Check if inside municipality
			for point in riverbank['coordinates'][0]:
				if inside_multipolygon(point, municipality_border):
					inside = True
					break

			if not inside:
				if close_to_border(riverbank['coordinates'][0], 100):
					inside = True

			if inside:

				if riverbank['type'] == "relation":
					riverbank_ways = [ ways[ member['ref'] ] for member in riverbank['member_patches'][0] ]  # Outer
				else:
					riverbank_ways = [ riverbank ]

				for way in riverbank_ways:
					for node_id in way['nodes']:
						for parent_id in list(nodes[ node_id ]['parents']):
							if parent_id in ways and "stream" in ways[ parent_id ]['topo']:
								river = ways[ parent_id ]

								if (river['tags']['waterway'] == "river"
										and not river['parents']
										and len(river['nodes']) > 4
										and node_id not in river['nodes'][:2] and node_id not in river['nodes'][-2:]
										and not river['incomplete']):

									# Split river way

									index = river['nodes'].index(node_id)

									element = {
										'type': 'way',
										'id': new_id(),
										'nodes': river['nodes'][ index : ],
										'tags': copy.deepcopy(river['tags']),
										'action': 'modify',
										'parents': river['parents'],
										'coordinates': [ river['coordinates'][0][ index : ] ],
										'incomplete': False,
										'topo': set(["stream"])
									}
									element['tags']['RIVERSPLIT'] = "yes"

									# To-do: Consider elvis, direction, bbox

									elements.append(element)
									ways[ element['id'] ] = element

									river['nodes'] = river['nodes'][ : index + 1 ]
									river['coordinates'] = [ river['coordinates'][0][ : index + 1 ] ]
									river['tags']['RIVERSPLIT'] = "yes"
									river['action'] = "modify"

									# Update node parents

									nodes[ node_id ]['parents'].add(element['id'])
									for new_node_id in element['nodes'][1:]:
										if river['id'] in nodes[ new_node_id ]['parents']:
											nodes[ new_node_id ]['parents'].remove(river['id'])
										nodes[ new_node_id ]['parents'].add(element['id'])

									count_split += 1

		if count_split > 0:
			message ("\tSplit %i river centerlines (for swapping)\n" % count_split)


	message ("\tRun time %s\n" % (timeformat(time.time() - lap)))



# Get elevation for one point/coordinate or for a list of points.
# Returns result for single point only. List of points are stored in elevations dict.
# Note: Slow api, approx 3 calls / second for single points, or quicker 35 points / second for batches of 50 points.

def load_elevation(input_nodes):

	if isinstance(input_nodes, tuple):
		if input_nodes in elevations:
			return elevations[ input_nodes ]
		node_list = [ input_nodes ]
	else:
		node_list = []
		for node in input_nodes:
			if node not in elevations:
				node_list.append(node)

	count_missing = 0
	count_total = len(node_list)

	dtm1_list = []
	lake_list = []

	for endpoint in ["datakilder/dtm1/punkt", "punkt"]:

		endpoint_list = node_list[:]
		node_list = []

		for i in range(0, len(endpoint_list), 50):
			message ("\r\t%i " % ((len(endpoint_list) - i)//50 * 50))

			nodes_string = json.dumps(endpoint_list[ i : i + 50 ]).replace(" ", "")
			url = "https://ws.geonorge.no/hoydedata/v1/%s?punkter=%s&geojson=false&koordsys=4258" % (endpoint, nodes_string)
			request = urllib.request.Request(url, headers=header)

			try:
				file = urllib.request.urlopen(request)
			except urllib.error.HTTPError as err:
				message("\r\t\t*** %s\n" % err)
				return None

			result = json.load(file)
			file.close()

			for node in result['punkter']:
				point = ( node['x'], node['y'] )
				if node['z'] is not None:
					elevations[ point ] = node['z']  # Store for possible identical request later
					if "datakilde" not in node and "dtm1" in endpoint:
						node['datakilde'] = "dtm1"

				elif endpoint == "punkt":  # Last pass
					count_missing += 1
					elevations[ point ] = None  # Some coastline points + Areas in North with missing DTM
#					message (" *** NO DTM ELEVATION: %s \n" % str(node))
#					create_point(point, {'ele': 'Missing'})  #, object_type = "DTM")
				else:
					node_list.append(point)  # One more try in next pass

	if isinstance(input_nodes, tuple):
		return elevations[ input_nodes ]

	if count_missing == count_total and count_total > 10:
		message ("\r\t*** NO ELEVATIONS FOUND - Perhaps API is currently down\n")
	elif count_missing > 0:
		message ("\r\t%i elevations not found\n" % count_missing)

	return True



# Get lake's elevation with decimals from DTM1.
# Run after SSR place names.

def get_lake_elevations():

	message ("Loading lake elevations...\n")

	lake_ele_count = 0
	ele_nodes = []
	lake_elevations = []

	for feature in features:
		if "water" in feature['topo'] and "ele" not in feature['tags']:

			if feature['area'] > min_ele_size:

				lake_node = None
				if "lake_node" in feature:
					lake_node = feature['lake_node']

				# Check that name coordinate is not on lake's island
				if lake_node:
					if not inside_multipolygon(lake_node, feature['coordinates']):
						lake_node = None

				# If name coordinate cannot be used, try centroid
				if lake_node is None:
					lake_node = polygon_centroid(feature['coordinates'][0])
					if not inside_multipolygon(lake_node, feature['coordinates']):
						lake_node = None

				# If fail, try midpoints across lake
				if lake_node is None:
					half = len(feature['coordinates'][0]) // 2
					for i in range(half):
						node1 = feature['coordinates'][0][i]
						node2 = feature['coordinates'][0][i + half]
						lake_node = ( 0.5 * (node1[0] + node2[0]), 0.5 * (node1[1] + node2[1]) )
						if not inside_multipolygon(lake_node, feature['coordinates']):
							lake_node = None 
						else:
							break

				# If all fail, just use coordinate of first node on lake perimeter
				if lake_node is None:
					lake_node = feature['coordinates'][0][0]

				if lake_node:
					ele_nodes.append(lake_node)
					lake_elevations.append({'feature': feature, 'center': lake_node})

	# Get elevations from api and assign to lakes

	load_elevation(ele_nodes)

	for lake in lake_elevations:
		if lake['center'] in elevations and elevations[ lake['center'] ] is not None:
			feature = lake['feature']
			feature['ele'] = max(elevations[ lake['center'] ], 0)
			if "ele" not in feature['tags'] and feature['area'] >= min_ele_size:
				feature['tags']['ele'] = str(int(max(elevations[ lake['center'] ], 0)))
				feature['action'] = "modify"
				lake_ele_count += 1

	message ("\r\t%i extra lake elevations found\n" % lake_ele_count)




# Load SSR place names from file.
# Two alternaitve sources; ssr2osm (preferred) or Obtitus files.

def load_ssr():

	# Check match with name endings

	def name_match(place, ssr_types, words):

		return (place['tags']['ssr:type'] in ssr_types
				and any(word == place['tags']['name'][-len(word):].lower() for word in words))


	# Load all SSR place names in municipality

	filename = "stedsnavn_%s_%s.geojson" % (municipality_id, municipality_name.replace(" ", "_"))
	folder_filename = os.path.expanduser(import_folder + filename)

	if os.path.isfile(filename) or os.path.isfile(folder_filename):
		ssr_source = "ssr2osm in CURRENT working folder"
		if not os.path.isfile(filename):
			filename = folder_filename
			ssr_source = "ssr2osm"
		file = open(filename)
		data = json.load(file)
		file.close()

		for feature in data['features']:
			tags = {}
			for key, value in iter(feature['properties'].items()):
				if "name" in key or key in ["ssr:stedsnr", "TYPE", "N100", "N50"]:
					if key == "TYPE":
						tags['ssr:type'] = value
					else:
						tags[ key ] = value
			entry = {
				'coordinate':  (feature['geometry']['coordinates'][0], feature['geometry']['coordinates'][1]),
				'tags': tags
			}
			ssr_places.append(entry)

	# Alternative source for SSR

	else:
		ssr_source = "obtitus"
		url = "https://obtitus.github.io/ssr2_to_osm_data/data/%s/%s.osm" % (municipality_id, municipality_id)
		request = urllib.request.Request(url, headers=header)

		try:
			file = urllib.request.urlopen(request)
		except urllib.error.HTTPError as err:
			message("\t\t*** %s\n" % err)
			return

		tree = ET.parse(file)
		file.close()
		root = tree.getroot()

		for node in root.iter('node'):
			tags = {}
			for tag in node.iter('tag'):
				if "name" in tag.get('k') or tag.get('k') in ["ssr:stedsnr", "ssr:type"]:
					tags[ tag.get('k') ] = tag.get('v')
			entry = {
				'coordinate': (float(node.get('lon')), float(node.get('lat'))),
				'tags': tags
			}

			# Split multiple equally ranked names in name=* ("likestilte navn")
			# No support for language suffixes (.no, .se, .fkv etc)

			if ";" in tags['name'] and " - " not in tags['name']:
				point = entry['coordinate']
				for name in tags['name'].split(";"):
					new_entry = copy.deepcopy(entry)
					new_entry['tags']['name'] = name
					alt_name = tags['name'].split(";")
					alt_name.remove(name)
					alt_name = ";".join(alt_name)
					if "alt_name" in tags:
						new_entry['tags']['alt_name'] = alt_name + ";" + new_entry['tags']['alt_name']
					else:
						new_entry['tags']['alt_name'] = alt_name
					new_entry['FIXME'] = "Chose equivalent name: " + tags['name']
					new_entry['coordinate'] = point
					point = (point[0], point[1] + 0.00002)
					ssr_places.append(new_entry)
			else:
				ssr_places.append(entry)

	# Modify place names

	lake_endings = ["vannene", "vanna", "vatna", "vannan", "vatnan", "vatni", "votni",
					"sjøene", "sjøa", "sjøan",
					"tjerna", "tjerne", "tjernan",  # "tjerni"
					"tjennene", "tjennane", "tjennin",
					"tjønnen", "tjønnan", "tjønnane", "tjønnin", "tjønnæ",
					"tjørna", "tjørnan", "tjørnene", "tjørnane", "tjørnin",  # "tjørni"
					"tjødnen", "tjødnene", "tjødnan", "tjødnane",
					"putta", "puttane", "kulpene", "dammene",
					"jávrrit", "luobbalat", "jávrrážat", "láddot", "láttut"]

	island_endings = ["øyene", "øyne", "øyan", "øyane", "øynan", "øynane", "øyna", "øyin", "øye", "øyrane",  # "øyni"
					"holmene", "holmane", "holman",
					"skjærene", "skjæra", "skjæran", "skjeran", "skjera", "steinan",
					"sullot", "sulložat"]

	count_modified = 0

	for place in ssr_places:

		new_type = ""

		# Modify place type for group of lakes and islands which have wrong type (will get lower priority)

		if name_match (place, ["vann"], lake_endings):
			new_type = "gruppeAvVann"

		elif name_match (place, ["tjern"], lake_endings):
			new_type = "gruppeAvTjern"

		elif name_match (place, ["øy", "øyISjø"], island_endings):
			new_type = place['tags']['ssr:type'].replace("øy", "øygruppe")

		elif name_match (place, ["holme"], island_endings):
			new_type = place['tags']['ssr:type'].replace("holme", "øygruppe")

		elif name_match (place, ["holmeISjø"], island_endings):
			new_type = place['tags']['ssr:type'].replace("holme", "holmegruppe")

		elif name_match (place, ["skjær"], island_endings):
			new_type = place['tags']['ssr:type'].replace("skjær", "øygruppe")

		elif name_match (place, ["skjærISjø"], island_endings):
			new_type = place['tags']['ssr:type'].replace("skjær", "holmegruppe")

		# Update place name type

		if new_type:
			place['tags']['ssr:type'] = new_type
			count_modified += 1


	message ("\t%i place names in SSR file from %s\n" % (len(ssr_places), ssr_source))
	if count_modified > 0:
		message ("\tModified %i place name types\n" % count_modified)



# Load place names from SSR within given bbox 

def get_ssr_name (feature, name_categories):

	# Internal function for ranking place names.
	# Larger score is better.

	def sort_place(place):

		n100_score = 1000
		if "N100" in place['tags']:
			n100_score = int(place['tags']['N100'])
		n50_score = 1000
		if "N50" in place['tags']:
			n50_score = int(place['tags']['N50'])

		score = ( name_categories.index(place['tags']['ssr:type']),
					n100_score,
					n50_score,
					- len(place['tags']['name'].split()),  # Priority to 2+ words
					int(place['tags']['ssr:stedsnr']) )  # Priority to oldest numbers

		return score


	global name_count

	if feature['type'] == "node":
		[ min_bbox, max_bbox ] = get_bbox(feature['coordinates'][0], perimeter=500)  # 500 meters perimeter to each side
	else:
		[ min_bbox, max_bbox ] = get_bbox(feature['coordinates'][0]) 

	polygon = feature['coordinates']

	found_places = []
	names = []

	# Find name in stored file

	for place in ssr_places[:]:
		if (min_bbox[0] <= place['coordinate'][0] <= max_bbox[0]
				and min_bbox[1] <= place['coordinate'][1] <= max_bbox[1]
				and place['tags']['ssr:type'] in name_categories
				and (feature['type'] == "Point" or inside_multipolygon(place['coordinate'], polygon))):

			# Special retagging for grave yard
			if place['tags']['ssr:type'] == "kirke":
				if "landuse" in feature['tags'] and feature['tags']['landuse'] == "cemetery":
					del feature['tags']['landuse']
					feature['tags']['OSM_landuse'] = "cemetery"
					feature['tags']['amenity'] = "grave_yard"
					feature['action'] = "modify"

			else:
				found_places.append(place)
				names.extend(place['tags']['name'].replace(" - ", ";").split(";"))  # Split multiple languages + variants

			ssr_places.remove(place)

	# Sort and select name

	if found_places:
		new_tags = {}
		found_places.sort(key=sort_place)

		# Establish alternative names for fixme tag
		alt_names = []
		alt_names_short = []
		sea = ("Sjø" in found_places[0]['tags']['ssr:type'])
		for place in found_places:
			source = ""
			if "N100" in place['tags']:
				source = "N100 "
			elif "N50" in place['tags']:
				source = "N50 "
			alt_names.append("%s [%s%s %s]" % (place['tags']['name'], source, place['tags']['ssr:type'], place['tags']['ssr:stedsnr']))
			if place['tags']['name'] not in alt_names_short:
				alt_names_short.append(place['tags']['name'])

		# Exit if SSR place name already is established
		if "ssr:stedsnr" in feature['tags'] and "name" in feature['tags']:
			found = False
			for place in found_places:
				if (place['tags']['ssr:stedsnr'] != feature['tags']['ssr:stedsnr']
						and not any(place['tags']['ssr:type'] == subtype for subtype in ["øygruppe", "gruppeAv", "delAv"])
						and place['tags']['name'] != feature['tags']['name']
						and ("alt_name" not in feature['tags'] or place['tags']['name'] not in feature['tags']['alt_name'].split(";"))):
#						and place['tags']['ssr:type'] != "kirke"):
					point = place['coordinate']
					tags = copy.deepcopy(place['tags'])
					tags['FIXME'] = "Insert " + tags.pop("ssr:type", None)
					create_point(point, tags)
					found = True
			if found:
				feature['tags']['FIXME'] = "Consider extra name: " + ", ".join(alt_names)
				if feature['tags']['name'] in alt_names_short:
					alt_names_short.remove(feature['tags']['name'])
				feature['tags']['ALT_NAME'] = ";".join(alt_names_short)
				feature['action'] = "modify"
			return found_places[0]['coordinate']

		# Check if OSM name is already present
		extra = 0
		if "name" in feature['tags']:
			if feature['tags']['name'] in alt_names_short:
				alt_names_short.remove(feature['tags']['name'])
			alt_names.insert(0, "%s [OSM]" % feature['tags']['name'])
			alt_names_short.insert(0, feature['tags']['name'])
			extra = 1

		if "nve_name" in feature:
			alt_names.append("%s [NVE]" % feature['nve_name'])
			extra += 1

		# Use N100 rank if present
		if any(["N100" in place['tags'] for place in found_places]):
			n100_places = [place for place in found_places if "N100" in place['tags']]
			new_tags = copy.deepcopy(n100_places[0]['tags'])

			if len(found_places) > 1:
				if len(n100_places) > 1 and n100_places[0]['tags']['N100'] == n100_places[1]['tags']['N100']:
					new_tags['FIXME'] = "Choose %s name: " % "N100" + ", ".join(alt_names)					
				else:
					new_tags['FIXME'] = "Verify %s name: " % "N100" + ", ".join(alt_names)
				alt_names_short.remove(new_tags['name'])
				if alt_names_short:
					new_tags['ALT_NAME'] = ";".join(alt_names_short)
			name_count += 1

		# Name already suggested by OSM data, so get ssr:stedsnr and any alternative names
		elif "name" in feature['tags'] and feature['tags']['name'] in names:
			name = feature['tags']['name']
			for place in found_places:
				# Avoid group names, often used by NVE
				if name in place['tags']['name'].replace(" - ", ";").split(";") and "gruppe" not in place['tags']['ssr:type']:
					new_tags = copy.deepcopy(place['tags'])

					if len(found_places) > 1:
						new_tags['FIXME'] = "Verify OSM name: " + ", ".join(alt_names)
						alt_names_short.remove(new_tags['name'])
						if alt_names_short:
							new_tags['ALT_NAME'] = ";".join(alt_names_short)
					name_count += 1
					break

		if not new_tags:  # Name not selected yet

			# Only one name found, or only one name of preferred type
			if len(found_places) == 1 or found_places[0]['tags']['ssr:type'] != found_places[1]['tags']['ssr:type']:
				new_tags = copy.deepcopy(found_places[0]['tags'])

				if len(found_places) > 1:
					new_tags['FIXME'] = "Verify name: " + ", ".join(alt_names)
					alt_names_short.remove(new_tags['name'])
					if alt_names_short:
						new_tags['ALT_NAME'] = ";".join(alt_names_short)
				name_count += 1

			# Not able to determine only one name
			else:
				# Select N50 name if available
				if any(["N50" in place['tags'] for place in found_places]):
					same_places = [ place for place in found_places if "N50" in place['tags'] ]
					if len(same_places) > 1 and same_places[0]['tags']['N50'] == same_places[1]['tags']['N50']:
						fixme = "Choose N50 name: " + ", ".join(alt_names)
					else:
						fixme = "Verify N50 name: " + ", ".join(alt_names)
				else:
					# If same type, select first in sorting (promote multiple words)
					same_places = [ place for place in found_places if place['tags']['ssr:type'] == found_places[0]['tags']['ssr:type'] ]
					fixme = "Choose name: " + ", ".join(alt_names)

				new_tags = copy.deepcopy(same_places[0]['tags'])
				new_tags['FIXME'] = fixme
				alt_names_short.remove(new_tags['name'])
				if alt_names_short:
					new_tags['ALT_NAME'] = ";".join(alt_names_short)

		# Warning for equal rank names ("sidestilte navn")

		if ";" in new_tags['name']:
			if "FIXME" in new_tags:
				new_tags['FIXME'] = new_tags['FIXME'].replace("Verify", "Choose")
			else:
				new_tags['FIXME'] = "Choose equivalent name: " + new_tags['name']

		# Create separate nodes for each alternative name

		if "FIXME" in new_tags:
			for place in found_places:
				point = place['coordinate']
				tags = copy.deepcopy(place['tags'])
				tags['FIXME'] = "Insert " + tags.pop("ssr:type", None)
				create_point(point, tags)

		# Updated tags and set as modified

		updated_tags = { key: feature['tags'][ key ] for key in feature['tags'] if key != "name" and key[:5] != "name:" }  # Omit old name tags
		updated_tags.update(new_tags)

		if feature['tags'] != updated_tags:
			for key, value in iter(feature['tags'].items()):
				if (key not in updated_tags
						or value != updated_tags[ key ]
							and not (key in ["name", "alt_name"]
								and ("name" in updated_tags and value in updated_tags['name'].split(";")
									or "alt_name" in updated_tags and value in updated_tags['alt_name'].split(";")))):
					updated_tags[ "OSM_" + key ] = value
			feature['tags'] = updated_tags
			feature['action'] = "modify"

		return found_places[0]['coordinate']



# Get place names for islands, glaciers etc.
# Place name categories: https://github.com/osmno/geocode2osm/blob/master/navnetyper.json

def merge_place_names():

	global name_count

	# Keep place names which did not get any hit

	def keep_unused_names(ssr_categories):

		nonlocal unused_count

		for place in ssr_places:
			if place['tags']['ssr:type'] in ssr_categories:
				point = place['coordinate']
				if place['tags']['ssr:type'] == "kirke":
					tags = {
						'FIXME': "Retag grave yard",
						'amenity': 'grave_yard'
					}
				else:
					tags = copy.deepcopy(place['tags'])
					tags['FIXME'] = "Insert " + tags.pop("ssr:type", None)

				create_point(point, tags)
				unused_count += 1


	# Update SSR place names which are already in OSM

	def check_existing_names(ssr_categories):

		nonlocal old_count

		ssr_stedsnr_places = {}
		for place in ssr_places:
			if place['tags']['ssr:type'] in ssr_categories and place['tags']['ssr:type'] != "kirke":
				ssr_stedsnr_places[ place['tags']['ssr:stedsnr'] ] = place

		for element in elements:
			if "ssr:stedsnr" in element['tags'] and element['tags']['ssr:stedsnr'] in ssr_stedsnr_places:
				ssr_place = ssr_stedsnr_places[ element['tags']['ssr:stedsnr'] ]

				for key, value in iter(ssr_place.items()):
					if "name" in key:
						if key in element['tags']:
							new_names = []
							for name in value.replace(" - ", ";").split(";"):
								if name not in element['tags'][ key ].replace(" - ", ";").split(";"):
									new_names.append(name)
							if new_names:
								element['tags'][ "UPDATE_" + key ] = ";".join(new_names)
						else:
							element['tags'][ "UPDATE_ " + key ] = value

				if ssr_place in ssr_places:
					ssr_places.remove(ssr_place)
					old_count += 1


	# Get place names for a category

	def get_category_place_names(osm_categories, ssr_categories):

		check_existing_names(ssr_categories)
		for feature in features:
			if any(topo in osm_categories for topo in feature['topo']):
				get_ssr_name(feature, ssr_categories)


	message ("Merge place names from SSR...\n")
	if not ssr_places:
		load_ssr()

	name_count = 0
	unused_count = 0
	old_count = 0

	# Get island names. Group names sorted last.

	name_category = ["øyISjø", "holmeISjø", "skjærISjø", "øy", "holme", "skjær", "øygruppeISjø", "øygruppe", "holmegruppeISjø"]  # Remove holmegruppeISjø ?
	check_existing_names(name_category)
	for feature in features:
		if "place" in feature['tags'] and feature['tags']['place'] in ["island", "islet"]:
			get_ssr_name(feature, name_category)

	keep_unused_names(name_category)

	# Get lake names + build list of lake center coordinate to get elevation. Group and part names sorted last.

	name_category = ["innsjø", "vann", "tjern", "høl", "lon", "pytt", "kanal", "gruppeAvVann", "gruppeAvTjern", "delAvInnsjø", "delAvVann"]
	check_existing_names(name_category)
	for feature in features:
		if "water" in feature['topo']:
			feature['lake_node'] = get_ssr_name(feature, name_category)

	keep_unused_names(name_category)

	# Get nanes for other features (areas)

#	get_category_place_names(["ElvBekk", "Elv"], ["elv", "elvesving", "lon"])	# River
	get_category_place_names(["glacier"], ["isbre", "fonn", "iskuppel"])  # Glacier
	get_category_place_names(["wetland"], ["myr", "våtmarksområde"])  # Wetland
	get_category_place_names(["cemetery"], ["gravplass", "kirke"])  # Cemetery
	get_category_place_names(["piste"], ["alpinanlegg", "skiheis"])  # Piste
	get_category_place_names(["landfill"], ["dam"])  # Dam
#	get_category_place_names(["Foss"], ["foss", "stryk"])  # Waterfall (point)

	# Clean up tags

	for feature in features:
		for tag in ["N100", "N50"]:
			if tag in feature['tags']:
				del feature['tags'][ tag ]

	message ("\t%i existing place names found in OSM\n" % old_count)
	message ("\t%i place names found\n" % name_count)
	message ("\t%i place names not matched but added as nodes\n" % unused_count)



# Get river/stream names

def get_river_names():

	message ("Merge river names from SSR...\n")

	if not ssr_places:
		load_ssr()

	# Build list of rivers/streams

	streams = []
	for way in ways.values():
		if ("stream" in way['topo'] and "tunnel" not in way['tags'] or "dam" in way['topo']) and not way['incomplete'] :
			way['min_bbox'], way['max_bbox'] = get_bbox(way['coordinates'][0], perimeter = 100)
			streams.append(way)

	name_count = 0
	unused_count = 0

	# Loop each place name to determine closest fit with river/stream

	for place in ssr_places:
		if place['tags']['ssr:type'] in ["elv", "elvesving", "bekk", "grøft", "foss", "stryk", "dam"]:
			min_distance = 100
			for stream in streams:
				if (stream['min_bbox'][0] <= place['coordinate'][0] <= stream['max_bbox'][0]
						and stream['min_bbox'][1] <= place['coordinate'][1] <= stream['max_bbox'][1]
						and not ("stream" in stream['topo'] and place['tags']['ssr:type'] == "dam")):
					distance, index = shortest_distance(place['coordinate'], stream['coordinates'][0])
					if distance < min_distance:
						min_distance = distance
						min_index = index
						found = stream

			if min_distance < 100:
				if place['tags']['ssr:type'] in ["foss", "stryk"]:  # Point feature
					if len(stream['coordinates']) > 2:  # Avoid tagging at end points
						if min_index == 0:
							min_index = 1
						elif min_index == len(stream['coordinates']) - 1:
							min_index = -2
					node = nodes[ found['nodes'][ min_index ] ]
					tags = copy.deepcopy(place['tags'])
					if place['tags']['ssr:type'] == "foss":
						tags['waterway'] = "waterfall"
					else:
						tags['waterway'] = "rapids"
					del tags['ssr:type']
					merge_tags(node, tags)
					name_count += 1
				else:
					if "names" not in found:
						found['names'] = []
					found['names'].append(place)  # Build list of all matched place names for feature

			else:
				# Create name node if no match 
				point = place['coordinate']
				tags = copy.deepcopy(place['tags'])
				if tags['ssr:type'] == "dam":
					tags['waterway'] = "dam"
				elif tags['ssr:type'] == "foss":
					tags['waterway'] = "waterfall"
				elif tags['ssr:type'] == "stryk":
					tags['waterway'] = "rapids"
				tags['FIXME'] = "Insert " + tags.pop("ssr:type", None)
				create_point(point, tags)
				unused_count += 1

	# Assign matched place name to feature

	for stream in streams:
		if "names" in stream:
			name_count += 1

			# Match with one place name
			if len(set(place['tags']['name'] for place in stream['names'])) == 1:
				for key, value in iter(stream['names'][0]['tags'].items()):
					if "name" in key or key in ["ssr:stedsnr", "TYPE"]:
						stream['tags'][ key ] = value
						stream['action'] = "modify"

			else:
				# Match with several place names

				name_list = []
				for place in stream['names']:
					source = ""
					if "N100" in place['tags']:
						source = " [N100]"
					elif "N50" in place['tags']:
						source = " [N50]"
					name_list.append(place['tags']['name'] + source)

				stream['tags']['FIXME'] = "Split waterway for names: " + ", ".join(name_list)
				stream['action'] = "modify"
				for place in stream['names']:
					point = place['coordinate']
					tags = copy.deepcopy(place['tags'])
					tags['FIXME'] = "Insert " + tags.pop("ssr:type", None)
					create_point(point, tags)	

	# Clean up tags

	for way in ways.values():
		for tag in ["N100", "N50"]:
			if tag in way['tags']:
				del way['tags'][ tag ]

	message ("\t%i place names found\n" % name_count)
	message ("\t%i place names not matched - added as nodes\n" % unused_count)



# Add wikidata tags for lakes - Under development

def get_wikidata():

	# Internal function to discover name match in tags

	def match_name(tags, target_name):

		for key, value in iter(lake['tags'].items()):
			if any(name_key == key or name_key + ":" in key for name_key in ["name", "alt_name", "old_name", "loc_name"]):
				for language_name in value.split(" - "):
					for name in value.split(";"):
						if name == target_name:
							return True
		return False


	message ("Loading wikidata for lakes ...\n")

	query = '''
	SELECT ?item ?label ?ssr ?nveid ?gnsid ?geonamesid ?loc ?forekomstLabel ?article ## Kan byttes ut med * for å få alle data
	{
		{
			SELECT distinct * {
				{ ?item wdt:P31/wdt:P279* wd:Q23397. } ## Søker her etter innsjø (Q23397) og alt som er underklasser (rekursivt) av innsjø
				UNION
				{ ?item wdt:P31/wdt:P279* wd:Q131681. }
				UNION
				{ ?item wdt:P31/wdt:P279* wd:Q3253281. }
#				?item wdt:P31 ?forekomst.
				?item wdt:P131 ?kommune. ## Ligger i en kommune
				?kommune wdt:P2504 "%s". ## Denne kommunen har norsk kommunenr som skal være det som er gitt som en streng
				optional {
					?item wdt:P5079 ?nveid . # NVE Innsjødatabase-ID (P5079)
				}
				optional {
					?item wdt:P2326 ?gnsid . # GNS-ID (P2326)
				}
				optional {
					?item wdt:P1566 ?geonamesid . # GeoNames-identifikator (P1566)
				}
				optional {
					?item wdt:P625 ?loc . # Geografisk posisjon 
				}
				optional {
					?item  wdt:P1850 ?ssr. # SSR stedsnummer (P1850)
				}
				optional {
					?article schema:about ?item.   # artikkel 
					?article schema:isPartOf <https://no.wikipedia.org/>. # Begrenset til no.wikipedia
				} 
			} LIMIT 1000 
		}
		SERVICE wikibase:label {
			bd:serviceParam wikibase:language "nb,en,de,fr,ja,es,ru,pt,it,zh,fa,ar,pl,nl,uk,tr,id,he,cs,sv,hu,fi,vi,ko,el,hi,bn,no,ca,ro,th,da,sr,bg,az,ms,et,uz,hr,sk,eu,hy,sl,lt,eo,ta,kk,lv,be,kn,sq,ur,mk" .
			?item rdfs:label ?label . ?item schema:description ?description. ?forekomst rdfs:label ?forekomstLabel
		}
	}''' % municipality_id

	url_endpoint = 'https://query.wikidata.org/sparql?'
	request = urllib.request.Request(url_endpoint + "query=" + urllib.parse.quote(query) + "&format=json", headers=header)
	file = urllib.request.urlopen(request)
	data = json.load(file)
	file.close()

	# Transform from SPARQL bindings

	wikidata_list = []
	wikidata_set = set()

	for record in data['results']['bindings']:
		wikidata = {}
		for key, value in iter(record.items()):
			wikidata[ key ] = value['value']
#			wikidata[ key ] = unicodedata.normalize('NFC', wikidata[ key ])
		wikidata_tag = wikidata['item'].split("/")[-1]
		if wikidata_tag not in wikidata_set:
			wikidata_list.append(wikidata)
			wikidata_set.add(wikidata_tag)

	# Build index for NVE ref and SSR

	wikidata_nve = {}
	wikidata_ssr = {}

	for wikidata in wikidata_list:
		if "nveid" in wikidata:
			wikidata_nve[ wikidata['nveid'] ] = wikidata
		if "ssr" in wikidata:
			wikidata_ssr[ wikidata['ssr']] = wikidata

	# Loop lakes and assign wikidata tag if match with SSR or NVE lake ref

	count_hits = 0
	count_label = 0

	for lake in features:
		if "water" in lake['topo'] and not lake['incomplete']:

			wikidata = None
			if "ref:nve:vann" in lake['tags'] and lake['tags']['ref:nve:vann'] in wikidata_nve:
				wikidata = wikidata_nve[ lake['tags']['ref:nve:vann'] ]
			elif "ssr:stedsnr" in lake['tags'] and lake['tags']['ssr:stedsnr'] in wikidata_ssr:
				wikidata = wikidata_ssr[ lake['tags']['ssr:stedsnr'] ]

			if wikidata is not None:
				wikidata_tag = wikidata['item'].split("/")[-1]
				new_tags = { 'wikidata': wikidata_tag }

				# Warning if no match with name tag
				if "wikidata" in lake and lake['tags']['wikidata'] != wikidata_tag:
					message ("\t*** Wikidata tag not matching: %s " % wikidata_tag)
					if wikidata['label'] != wikidata_tag:
						message (wikidata['label'] + "\n")
						new_tags["WIKIDATA_LABEL"] = wikidata['label']
					else:
						message ("\n")
						count_label += 1
				elif wikidata['label'] == wikidata_tag:
#					message ("\t*** Missing label in Wikidata: %s\n" % wikidata_tag)
					count_label += 1
				elif not match_name(lake['tags'], wikidata['label']):
					message ("\t*** Wikidata name not matching: %s %s\n" % (wikidata_tag, wikidata['label']))
					new_tags["WIKIDATA_LABEL"] = wikidata['label']

				merge_tags(lake, new_tags)
				wikidata['found'] = True
				count_hits += 1

	# Create node for remaining unmatched wikidata

	for wikidata in wikidata_list:
		if "found" not in wikidata:
			tags = {
				'wikidata': wikidata['item'].split("/")[-1],
				'name': wikidata['label'],
				'FIXME': "Insert wikidata for lake"
			}
			point = wikidata['loc'].strip("Point()").split(" ")
			point = ( float(point[0]), float(point[1]) )
			create_point(point, tags)

	message ("\tMerged %i of %i Wikidata tags\n" % (count_hits, len(wikidata_list)))
	message ("\t%i missing labels\n" % count_label)



# Convert topo relations into ways if possible

def simplify_relations():

	# Check if two dict of tags are different

	def diff_tags(tags1, tags2):

		diff = set(tags.items()) ^ set(tags2.items())
		for key, value in diff:
			if key not in ["source", "source:date", "SIMPLIFY"]:
				return True
		return False


	def intersect_tags(tags1, tags2):

		diff = set(tags.items()) & set(tags.items())
		for key, value in diff:
			if key not in ["source", "source:date", "SIMPLIFY"]:
				return True
		return False


	message ("Simplify relations ...\n")
	count_ways = 0
	count_relations = 0

	for feature in features:
		if feature['type'] != "relation" or "coordinates" not in feature or feature['incomplete']:
			continue

		# Check each patch (outer, inner) for simplification

		for patch in feature['member_patches']:

			ok = True
			tags = ways[ patch[0]['ref'] ]['tags']
			parents = ways[ patch[0]['ref'] ]['parents']

			# Check if simplification should not be done

			if (any("coordinates" not in relations[ parent ] for parent in parents)
					or intersect_tags(tags, feature['tags']) and len(feature['member_patches']) == 1):
				ok = False

			else:
				for member in patch:
					way = ways[ member['ref'] ]

					if (way['incomplete'] or way['parents'] != parents or diff_tags(tags, way['tags'])
							or member['role'] == "inner" and len(patch) == 1
							or member['role'] == "outer" and len(patch) == 1 and len(feature['member_patches']) > 1):
						ok = False
						break

					if not way['nodes']:
						message ("Empty 1: %s\n%s\n" % (str(relation), str(way)))						

					# Should not intersect with grids, even when not connected to grid
					for node_id in [ way['nodes'][0], way['nodes'][-1] ]:
						node = nodes[ node_id ]
						if (abs(node['lat'] - round(node['lat'] * 20) /  20) < grid_limit
								or abs(node['lon'] - round(node['lon'] * 20) /  20) < grid_limit):
							ok = False
							break

			# Combine relation members into one way

			if ok:
				members = [ member['ref'] for member in patch ]
				sorted_members = sorted(members, key=lambda member: len(ways[ member ]['nodes']), reverse=True)  # Largest way

				keep_way = ways[ sorted_members[0] ]  # Full ring concatenated into this way
				keep_way['tags']['SIMPLIFY'] = str(feature['id'])
				keep_way['action'] = "modify"

				# Concatenate nodes and delete ways

				if len(members) == 1 or ways[ members[0] ]['nodes'][-1] in [ ways[ members[1] ]['nodes'][0], ways[ members[1] ]['nodes'][-1] ]:
					new_nodes = [ ways[ members[0] ]['nodes'][0] ]
				else:
					new_nodes = [ ways[ members[0] ]['nodes'][-1] ]

				for member in patch:
					way = ways[ member['ref'] ]

					if new_nodes[-1] == way['nodes'][0]:
						new_nodes.extend(way['nodes'][1:])
					else:
						new_nodes.extend(list(reversed(way['nodes']))[1:])

					for node_id in way['nodes']:
						nodes[ node_id ]['parents'].add(keep_way['id'])
					if way['id'] != keep_way['id']:
						delete_way(way)

				# Reverse coordinates if needed (clockwise)

				coordinates = [ ( nodes[ node ]['lon'], nodes[ node ]['lat'] ) for node in new_nodes ]
				area = polygon_area(coordinates)
				if area < 0 and not("natural" in keep_way['tags'] and keep_way['tags']['natural'] == "coastline"):
					coordinates.reverse()
					new_nodes.reverse()
				keep_way['nodes'] = new_nodes
				keep_way['coordinates'] = [ coordinates ]

				# Update members in parent relations

				outer = False
				for parent in keep_way['parents']:
					relation = relations[ parent ]
					for parent_patch in relation['member_patches']:
						for member in parent_patch[:]:
							if member['ref'] in members and member['ref'] != keep_way['id']:
								parent_patch.remove(member)

					relation['members'] = [ member for relation_patch in relation['member_patches'] for member in relation_patch ]  # Flat list
					relation['action'] = "modify"

				count_ways += len(members)

		# Swap relation with way if only one patch

		if ok and len(feature['member_patches']) == 1:

			merge_tags(keep_way, feature['tags'])
			del keep_way['tags']['type']  # type=multipolygon
			keep_way['topo'] = feature['topo'].copy()
			keep_way['parents'].remove(feature['id'])

			feature['incomplete'] = True
			feature['members'] = []
			del feature['coordinates']
			feature['action'] = "delete"

			feature = keep_way  # Replace feature
			count_relations += 1

	message ("\tJoined %i ways and converted %i relations into ways\n" % (count_ways, count_relations))



# Clean up certain tags

def clean_elements():

	for element in elements:
		if "action" in element and element['action'] == "modify":
			for key in list(element['tags']):
				if (key in ["source:date", "created_by", "N50", "N100", "ssr:type", "ssr:gruppe", "ssr:hovedgruppe", "ssr:dato"]
						or key == "source" and any(word in element['tags'][ key ] for word in disregard_sources)):
					del element['tags'][ key ]



# Indent XML output

def indent_tree(elem, level=0):
    i = "\n" + level*"  "
    if len(elem):
        if not elem.text or not elem.text.strip():
            elem.text = i + "  "
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
        for elem in elem:
            indent_tree(elem, level+1)
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
    else:
        if level and (not elem.tail or not elem.tail.strip()):
            elem.tail = i



# Save osm file

def save_file(filename, elements):

	message ("Save to '%s' file...\n" % filename)

	clean_elements()  # Clean up tags
	root = ET.Element("osm", version="0.6", generator="topofix v" + version, upload="false")

	for element in elements:

		xml_element = ET.Element(element['type'], id=str(element['id']))

		for attribute in ["lat", "lon", "action", "version", "changeset", "timestamp", "user", "uid"]:
			if attribute in element:
				xml_element.set(attribute, str(element[ attribute ]))

		if "nodes" in element:
			for node_id in element['nodes']:
				xml_nd = ET.Element("nd", ref=str(node_id))
				xml_element.append(xml_nd)

		if "members" in element:
			for member in element['members']:
				xml_member = ET.Element("member", type=member['type'], ref=str(member['ref']), role=member['role'])
				xml_element.append(xml_member)

		if "tags" in element:
			for key, value in iter(element['tags'].items()):
				if value and value is not None:
					xml_tag = ET.Element("tag", k=key, v=value)
					xml_element.append(xml_tag)

		root.append(xml_element)
			
	root.set("upload", "false")
	indent_tree(root)
	tree = ET.ElementTree(root)
	tree.write(filename, encoding='utf-8', method='xml', xml_declaration=True)

	message ("\t%i relations, %i ways saved\n" % (len(relations), len(ways)))



# Main program

if __name__ == '__main__':

	start_time = time.time()
	message ("\ntopofix v%s\n\n" % version)

	# Global data structure

	elements = []
	nodes = {}
	ways = {}
	relations = {}
	features = []
	elevations = {}
	ssr_places = []

	# Parse parameters

	if len(sys.argv) < 2 or sys.argv[1][0] == "-":
		message ("Please provide municipality name and -options\n")
		sys.exit()

	# Get municipality and set filenames

	municipality_query = sys.argv[1]
	municipality_id, municipality_name, municipality_bbox = get_municipality_name(municipality_query)
	if municipality_id is None:
		sys.exit("Municipality '%s' not found\n" % municipality_query)

	message ("Municipality: %s %s\n" % (municipality_id, municipality_name))

	output_filename = "topofix_%s_%s.osm" % (municipality_id, municipality_name.replace(" ", "_"))

	if len(sys.argv) > 2 and ".osm" in sys.argv[2]:
		input_filename = sys.argv[2]
	else:
		input_filename = ""
		if "-merge" in sys.argv and "-mergeprep" not in sys.argv and "-file" not in sys.argv:
			input_filename = output_filename.replace(".osm", "") + "_merge.osm"
			if not os.path.isfile(input_filename):
				sys.exit("Please provide OSM filename with FIXME=Merge/Split tags\n")

	output_filename = "topofix_%s_%s.osm" % (municipality_id, municipality_name.replace(" ", "_"))

	permitted_arguments = ["-overlap", "-mergeprep", "-merge", "-simplify", "-water", "-river", "-allriver", "-extrariver",
							"-island", "-wikidata", "-debug", "-nve", "-elvis"]

	for argument in sys.argv[2:]:
		if ".osm" not in argument and argument not in permitted_arguments:
			if argument != "-help":
				message ("Did not recognize '%s'.\n" % argument)
			sys.exit ("Permitted arguments:\n\t%s\n" % (", ".join(permitted_arguments)))

	if "-debug" in sys.argv:
		debug = True

	if "-nve" in sys.argv:
		nve_output = True

	message ("\n")

	# Process data

	if "-elvis" in sys.argv:
		get_nve_streams(nve_output_only=True)
		sys.exit()

	if input_filename:
		load_osm_file(input_filename)
	else:
		load_osm_overpass()

	fix_relation_order()
	prepare_features()

	if "-overlap" in sys.argv:
		fix_overlapping_ways()

	if "-simplify" in sys.argv:
		simplify_relations()
		combine_grid_lines()

	if "-mergeprep" in sys.argv:
		if "-merge" in sys.argv:
			identify_touching_relations(merge_grids=False)
		else:
			identify_touching_relations(merge_grids=True)

	if "-merge" in sys.argv:
		merge_touching_relations()
		message ("\tTip: Search for '*[eval(osm_id()=-636079)]' with 'MapCSS' selected to get negative id's\n")

	if "-water" in sys.argv:
		fix_water_tags()
		get_nve_lakes()
		create_islands()
		merge_place_names()
		get_lake_elevations()

	if "-island" in sys.argv:
		create_islands()

	if "-wikidata" in sys.argv:
		get_wikidata()

	if "-river" in sys.argv or "-allriver" in sys.argv or "-extrariver" in sys.argv:
		split_streams()
		get_river_names()
		if "-allriver" in sys.argv:
			get_nve_streams(add_all_centerlines=True, add_short_connections=True)
		elif "-extrariver" in sys.argv:
			get_nve_streams(add_short_connections=True)
		else:
			get_nve_streams()

	save_file(output_filename, elements)

	duration = time.time() - start_time
	message ("\tTotal run time %s (%i ways per second)\n\n" % (timeformat(duration), int(len(ways) / duration)))
