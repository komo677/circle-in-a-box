import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from tkinter import filedialog
import math
import os
import random
import time # To measure execution time
import itertools # For combinations
import copy # For deep copying point lists
import traceback # Import traceback module for detailed error printing

# --- Try importing necessary library for WebView ---
try:
    import webview # Use pywebview library
    WEBVIEW_AVAILABLE = True
except ImportError:
    WEBVIEW_AVAILABLE = False

# --- Global variables ---
generated_svg_content_best = None # SVG for the best result found
generated_svg_content_final = None # SVG for the final result at the end
preview_html_content_best = None # HTML for the best result
preview_html_content_final = None # HTML for the final result
show_preview_button = None # To enable/disable the preview button for best result
show_final_button = None   # To enable/disable the preview button for final result
download_button = None # To enable/disable the download button (downloads the best result)

# Store the points separately
overall_best_points_global = []
final_points_after_refinement = []


# --- Constants ---
EPSILON = 1e-9 # Small tolerance for floating point comparisons

def calculate_polygon_points(num_sides, cx, cy, radius, rotation_offset_degrees=0):
    """Calculates the vertex coordinates for a regular polygon."""
    points = []
    angle_step = 360 / num_sides
    rotation_offset_rad = math.radians(rotation_offset_degrees)

    for i in range(num_sides):
        angle_rad = math.radians(angle_step * i) - rotation_offset_rad
        x = cx + radius * math.cos(angle_rad)
        y = cy + radius * math.sin(angle_rad)
        # Use .7g for 7 significant digits
        points.append(f"{x:.7g},{y:.7g}")
    return " ".join(points)

def parse_points_string(points_str):
    """Parses the SVG points string into a list of (x, y) tuples."""
    vertices = []
    pairs = points_str.split(' ')
    for pair in pairs:
        if pair:
            try:
                x_str, y_str = pair.split(',')
                vertices.append((float(x_str), float(y_str)))
            except ValueError:
                print(f"警告: 点のペア '{pair}' を解析できませんでした。") # Warning: Could not parse point pair
                continue
    return vertices

def point_segment_distance_sq(px, py, x1, y1, x2, y2):
    """
    Calculates the squared shortest distance from a point (px, py)
    to a line segment ((x1, y1), (x2, y2)).
    """
    seg_len_sq = (x2 - x1)**2 + (y2 - y1)**2
    if seg_len_sq < EPSILON: # Segment is essentially a point
        return (px - x1)**2 + (py - y1)**2

    # Project point onto the line containing the segment
    dot_product = ((px - x1) * (x2 - x1) + (py - y1) * (y2 - y1))
    # Handle case where segment length is zero or near zero
    if seg_len_sq < EPSILON:
        t = 0.0
    else:
        t = dot_product / seg_len_sq

    t = max(0, min(1, t)) # Clamp t to [0, 1] to stay on the segment

    # Coordinates of the closest point on the segment
    closest_x = x1 + t * (x2 - x1)
    closest_y = y1 + t * (y2 - y1)

    # Squared distance from the point to the closest point on the segment
    dist_sq = (px - closest_x)**2 + (py - closest_y)**2
    return dist_sq

def is_point_on_boundary(px, py, vertices, tolerance_sq=EPSILON**2):
    """Checks if a point is on the boundary of the polygon."""
    n = len(vertices)
    if n < 2: return False # Need at least 2 vertices for an edge
    p1x, p1y = vertices[-1] # Start with edge from last to first vertex
    for i in range(n):
        p2x, p2y = vertices[i]
        dist_sq = point_segment_distance_sq(px, py, p1x, p1y, p2x, p2y)
        if dist_sq < tolerance_sq:
            return True # Point is on or very close to this edge
        p1x, p1y = p2x, p2y # Move to next edge
    return False

def is_point_strictly_inside_polygon(px, py, vertices):
    """Checks if a point (px, py) is strictly inside a polygon using Ray Casting."""
    n = len(vertices)
    if n < 3: return False
    # First, check if it's on the boundary, if so, it's not strictly inside
    if is_point_on_boundary(px, py, vertices):
        return False

    # Ray casting algorithm
    inside = False
    p1x, p1y = vertices[0]
    for i in range(n + 1):
        p2x, p2y = vertices[i % n]
        # Check if ray crosses edge (handle horizontal edges and vertices carefully)
        if p1y == p2y: # Horizontal edge: ray only crosses if endpoint is crossed
            pass # Handled by boundary check or vertex check essentially
        elif py > min(p1y, p2y) and py <= max(p1y, p2y):
             # Calculate x-intersection, avoid division by zero for vertical/near-vertical
             if abs(p2y - p1y) > EPSILON:
                 xinters = (py - p1y) * (p2x - p1x) / (p2y - p1y) + p1x
             else: # Vertical edge
                 xinters = p1x # or p2x

             # Only count crossings strictly to the left of the point
             if px < xinters - EPSILON:
                 inside = not inside

        p1x, p1y = p2x, p2y
    return inside


def is_point_inside_or_on_boundary(px, py, vertices):
    """Checks if point is inside or on the boundary."""
    # Check boundary first using distance, which is generally robust
    if is_point_on_boundary(px, py, vertices):
        return True
    # If not on boundary, check if it's strictly inside
    if is_point_strictly_inside_polygon(px, py, vertices):
         return True
    return False


def min_sq_distance_in_set(point_set):
    """Calculates the minimum squared distance between any pair of points in a set."""
    min_d2 = float('inf')
    n = len(point_set)
    if n < 2:
        return min_d2 # Cannot calculate distance with less than 2 points

    for i in range(n):
        for j in range(i + 1, n):
            p1 = point_set[i]
            p2 = point_set[j]
            dx = p1[0] - p2[0]
            dy = p1[1] - p2[1]
            dist_sq = dx*dx + dy*dy
            min_d2 = min(min_d2, dist_sq)
    return min_d2

def find_min_dist_pairs(point_set, min_dist_sq):
    """Finds all pairs of points in the set with the minimum squared distance."""
    pairs = []
    n = len(point_set)
    if n < 2: return pairs
    if min_dist_sq == float('inf'): return pairs # Avoid issues if only one point

    for i in range(n):
        for j in range(i + 1, n):
            p1 = point_set[i]
            p2 = point_set[j]
            dx = p1[0] - p2[0]
            dy = p1[1] - p2[1]
            dist_sq = dx*dx + dy*dy
            # Use tolerance when comparing floating point distances
            if abs(dist_sq - min_dist_sq) < EPSILON:
                pairs.append(((p1[0], p1[1]), (p2[0], p2[1]))) # Store coordinates directly
    return pairs


def find_initial_best_grid_comb(num_points_target, polygon_vertices, num_divisions, time_limit_sec, cx, cy, circumradius):
    """
    Performs exhaustive search on grid points (based on circumcircle square) for initial placement.
    Returns: (list of best points, bool timeout, dict grid_info, list valid_grid_points)
    """
    grid_info = {}
    valid_grid_points = []
    best_point_set = []
    timed_out = False
    max_min_dist_sq_found = -1.0

    if not polygon_vertices or len(polygon_vertices) < 3: return [], False, {}, []
    if num_divisions < 1: return [], False, {}, []
    if num_points_target < 2: return [], False, {}, []

    start_calculation_time = time.time()

    # 1. Define grid based on circumscribing circle's square
    grid_radius = circumradius # Use circumradius for the square bounds
    min_coord = cx - grid_radius
    max_coord = cx + grid_radius
    grid_size = 2 * grid_radius

    grid_info = {
        'cx': cx, 'cy': cy, 'radius': grid_radius, # Store circle info
        'min_x': min_coord, 'max_x': max_coord,
        'min_y': min_coord, 'max_y': max_coord, # Use same bounds for square
        'num_divisions': num_divisions
    }

    if grid_size < EPSILON:
        print("警告: グリッド基準となる円のサイズがほぼゼロです。") # Warning: Grid reference circle size is near zero.
        step = 0
    else:
        step = grid_size / num_divisions

    grid_info['step_x'] = step # Store step size (same for x and y)
    grid_info['step_y'] = step

    # 2. Generate Grid Points and Filter
    for i in range(num_divisions + 1):
        px = min_coord + i * step
        for j in range(num_divisions + 1):
            py = min_coord + j * step
            if is_point_inside_or_on_boundary(px, py, polygon_vertices):
                valid_grid_points.append((px, py))

    num_valid_grid_points = len(valid_grid_points)
    print(f"  初期探索: 有効な格子点の数: {num_valid_grid_points}")

    if num_valid_grid_points < num_points_target:
        print(f"  初期探索エラー: 有効な格子点 ({num_valid_grid_points}) が要求数 ({num_points_target}) より少ないです。")
        return [], False, grid_info, valid_grid_points

    # 3. Exhaustive Combination Search with Timeout
    combination_count = 0
    try:
        num_combinations_est = math.comb(num_valid_grid_points, num_points_target)
        print(f"  初期探索: 計算対象の組み合わせ数 (推定): {num_combinations_est:,}")
        if num_combinations_est > 500_000: # Lower warning threshold
             print(f"  初期探索警告: 組み合わせが非常に多い ({num_combinations_est:,})")
    except (OverflowError, ValueError):
         print("  初期探索警告: 組み合わせ数が大きすぎて推定できません。")

    try:
        for current_set in itertools.combinations(valid_grid_points, num_points_target):
            combination_count += 1
            current_min_d2 = min_sq_distance_in_set(current_set)
            # Use >= to handle the first valid case correctly
            if current_min_d2 >= max_min_dist_sq_found:
                # Add tolerance check: only update if significantly better or first
                if current_min_d2 > max_min_dist_sq_found + EPSILON or max_min_dist_sq_found < 0:
                    max_min_dist_sq_found = current_min_d2
                    best_point_set = list(current_set)

            if combination_count % 500 == 0:
                elapsed_time = time.time() - start_calculation_time
                if elapsed_time > time_limit_sec:
                    print(f"  初期探索タイムアウト: {time_limit_sec}秒を超えました。")
                    timed_out = True
                    break

        if not timed_out:
             elapsed_time = time.time() - start_calculation_time
             if elapsed_time > time_limit_sec:
                  print(f"  初期探索タイムアウト: {time_limit_sec}秒を超えました（ループ終了後）。")
                  timed_out = True

    except MemoryError:
         print("  初期探索メモリエラー: 組み合わせの処理中にメモリが不足しました。")
         timed_out = True # Treat as timeout
    except Exception as e:
         print(f"  初期探索中に予期せぬエラー: {e}")
         return best_point_set, False, grid_info, valid_grid_points # Return what we have

    result_status = "完了" if not timed_out else "タイムアウト"
    final_min_d = math.sqrt(max_min_dist_sq_found) if max_min_dist_sq_found >= 0 else 0.0
    print(f"  初期探索 {result_status}: 最良セット発見 (最短距離 approx {final_min_d:.3f})")

    if not best_point_set:
         print("  初期探索: 有効な組み合わせが見つかりませんでした。")

    return best_point_set, timed_out, grid_info, valid_grid_points


def refine_placement_neighbor_combinations_v3(initial_points, polygon_vertices, grid_info, max_iterations, time_limit_sec):
    """
    Refines placement by exhaustively checking combinations of neighbor positions
    (excluding current position) at each iteration with adaptive step size.
    Applies the best combination found in each iteration. Tracks the overall best.

    Args:
        initial_points (list): List of (x, y) tuples for initial placement.
        polygon_vertices (list): List of (x, y) tuples for polygon vertices.
        grid_info (dict): Dictionary containing initial grid parameters ('step_x', 'step_y').
        max_iterations (int): Maximum number of refinement iterations.
        time_limit_sec (float): Maximum time allowed for refinement in seconds.

    Returns:
        tuple: (list of best points found, list of points at final iteration, bool indicating if timed out)
    """
    if not initial_points or len(initial_points) < 2:
        return initial_points, initial_points, False

    # Keep track of the best configuration found across all iterations
    overall_best_points = copy.deepcopy(initial_points) # Start with initial as tuple list
    overall_max_min_d2 = min_sq_distance_in_set(overall_best_points)

    current_points = list(initial_points) # Use list of tuples for current state
    timed_out = False
    start_refinement_time = time.time()
    iteration_count = 0

    initial_step_x = grid_info.get('step_x', 1.0)
    initial_step_y = grid_info.get('step_y', 1.0)

    print(f"ステップ2: 近傍全組み合わせ改善を開始 (最大反復: {max_iterations}, 最大時間: {time_limit_sec}秒)...") # Step 2: Starting neighbor combination refinement...

    while iteration_count < max_iterations:
        iteration_count += 1
        elapsed_time = time.time() - start_refinement_time
        if elapsed_time > time_limit_sec:
            print(f"改善タイムアウト: {time_limit_sec}秒を超えました。") # Refinement Timeout: Exceeded {} seconds.
            timed_out = True
            break

        print(f" 改善反復 {iteration_count}/{max_iterations}...")

        # Calculate neighbor distance for this iteration
        divisor = 2**(iteration_count) # Start with step/2 in first iteration (k=1)
        current_neighbor_dist_x = initial_step_x / divisor
        current_neighbor_dist_y = initial_step_y / divisor

        neighbor_offsets = [ # Exclude (0, 0) offset
            (-current_neighbor_dist_x, -current_neighbor_dist_y), (0, -current_neighbor_dist_y), (+current_neighbor_dist_x, -current_neighbor_dist_y),
            (-current_neighbor_dist_x, 0)                        ,                               (+current_neighbor_dist_x, 0)                        ,
            (-current_neighbor_dist_x, +current_neighbor_dist_y), (0, +current_neighbor_dist_y), (+current_neighbor_dist_x, +current_neighbor_dist_y),
        ]

        # 1. Generate candidate positions for each point (neighbors only)
        candidate_sets = []
        possible_to_generate = True
        for i in range(len(current_points)):
            px, py = current_points[i]
            point_candidates = []
            for dx, dy in neighbor_offsets: # Iterate through 8 neighbors
                nx, ny = px + dx, py + dy
                if is_point_inside_or_on_boundary(nx, ny, polygon_vertices):
                    point_candidates.append((nx, ny))
            if not point_candidates:
                 # If no valid neighbors, the only candidate is the current position
                 print(f"警告: 点 {i} ({px:.2f},{py:.2f}) の有効な近傍候補が見つかりません。元の位置を維持します。") # Warning: No valid neighbor candidates found for point {}. Maintaining original position.
                 point_candidates.append((px, py)) # Add original position as the only candidate
            candidate_sets.append(point_candidates)

        # 2. Evaluate all combinations of candidate positions
        best_combination_this_iter = list(current_points) # Default to current if no better found
        max_min_d2_this_iter = -1.0 # Initialize to find the max min_d2
        comb_count_this_iter = 0
        iter_start_time = time.time()
        inner_timed_out = False

        # Estimate combinations for this iteration
        try:
            num_combinations_iter_est = 1
            for s in candidate_sets: num_combinations_iter_est *= len(s)
            print(f"  反復{iteration_count}: 評価する組み合わせ数 (推定): {num_combinations_iter_est:,}") # Iter {}: Combinations to evaluate (estimated):
            if num_combinations_iter_est > 100_000: # Warning threshold per iteration
                 print(f"  反復{iteration_count} 警告: 組み合わせが多いです。") # Iter {} Warning: High number of combinations.
        except OverflowError:
             print(f"  反復{iteration_count} 警告: 組み合わせ数が大きすぎます。") # Iter {} Warning: Number of combinations is too large.

        try:
            for current_combination in itertools.product(*candidate_sets):
                comb_count_this_iter += 1
                current_min_d2 = min_sq_distance_in_set(current_combination)

                if current_min_d2 > max_min_d2_this_iter: # Find combination with max min_d2
                    max_min_d2_this_iter = current_min_d2
                    best_combination_this_iter = list(current_combination)

                # Check time limit within the inner loop
                if comb_count_this_iter % 5000 == 0: # Check less frequently inside
                    iter_elapsed = time.time() - start_refinement_time
                    if iter_elapsed > time_limit_sec:
                        print(f"改善タイムアウト(内部): {time_limit_sec}秒を超えました。") # Refinement Timeout (Internal): Exceeded {} seconds.
                        timed_out = True
                        inner_timed_out = True
                        break # Break inner loop (itertools.product)

            if timed_out: break # Break outer loop (while)

        except MemoryError:
            print("メモリエラー: 近傍組み合わせの処理中にメモリが不足しました。") # Memory Error: Ran out of memory while processing neighbor combinations.
            messagebox.showerror("メモリエラー", "近傍組み合わせの処理中にメモリが不足しました。\n反復回数や点の数を減らしてください。")
            timed_out = True # Treat as timeout
            break # Break outer loop (while)
        except Exception as e:
            print(f"近傍組み合わせ計算中に予期せぬエラー: {e}") # Unexpected error during neighbor combination calculation:
            messagebox.showerror("計算エラー", f"近傍組み合わせ計算中にエラーが発生しました:\n{e}")
            break # Break outer loop (while)

        # 3. Update current_points and overall_best_points
        # Always update current_points to the best combination found in this iteration
        current_points = best_combination_this_iter

        # Check if this new state is better than the overall best found so far
        current_best_iter_min_d2 = max_min_d2_this_iter # Min dist of the chosen combination
        if current_best_iter_min_d2 > overall_max_min_d2 + EPSILON:
            overall_max_min_d2 = current_best_iter_min_d2
            overall_best_points = copy.deepcopy(current_points) # Store a copy
            print(f"  反復{iteration_count}: 新しい全体最適値を発見: {math.sqrt(overall_max_min_d2):.4g}") # New overall best found


    end_refinement_time = time.time()
    final_points_at_end = list(current_points) # Final state when loop ended
    placed_count = len(overall_best_points) # Return the overall best
    final_min_d_overall = math.sqrt(overall_max_min_d2) if overall_max_min_d2 >= 0 else 0.0
    result_status = "完了" if not timed_out else "タイムアウト"
    print(f"近傍組み合わせ改善 {result_status}: {placed_count}個の点を配置 (記録された最良最短距離 approx {final_min_d_overall:.4g}, 時間 {end_refinement_time - start_refinement_time:.2f}秒)") # Neighbor Combination Refinement {}: Placed {} points (best min dist approx {}, time {} seconds)

    if timed_out:
         messagebox.showinfo("タイムアウト", f"指定された時間または反復回数内に改善処理が完了しませんでした。\n反復中に見つかった最良の配置を表示します。") # Timeout: Refinement did not complete within the specified time/iterations. Displaying the best placement found during iterations.

    # Return the overall best points AND the points at the final iteration
    return overall_best_points, final_points_at_end, timed_out


def show_actual_preview_window(best_or_final):
    """Creates and starts a pywebview window for either best or final result."""
    global preview_html_content_best, preview_html_content_final
    html_to_show = None
    title = "SVG Preview"

    if best_or_final == "best" and preview_html_content_best:
        html_to_show = preview_html_content_best
        title = "SVG Preview (Best Found)"
    elif best_or_final == "final" and preview_html_content_final:
        html_to_show = preview_html_content_final
        title = "SVG Preview (Final State)"
    else:
         messagebox.showwarning("プレビュー不可", "表示するSVGデータが生成されていません。") # Cannot Preview: SVG data to display has not been generated.
         return

    if not WEBVIEW_AVAILABLE:
         messagebox.showerror("ライブラリエラー", "pywebviewライブラリが見つかりません。") # Library Error: pywebview library not found.
         return

    try:
        # Create and start the window. This will block the main thread (Tkinter GUI)
        # until the preview window is closed.
        webview.create_window(title, html=html_to_show, width=350, height=350, resizable=True)
        webview.start() # Runs the webview event loop
        print(f"情報: {title} ウィンドウを閉じました。") # Info: Closed {} window.
    except NameError:
         print("エラー: webviewモジュールが見つかりません。") # Error: webview module not found.
    except Exception as e:
        print(f"プレビューウィンドウの表示中にエラー: {e}") # Error displaying preview window:
        messagebox.showerror("プレビューエラー", f"プレビューウィンドウの表示中にエラー:\n{e}") # Preview Error: Error displaying preview window:

def generate_svg_content(points_to_draw, timed_out, grid_info, valid_grid_points, min_dist_pairs, svg_width, svg_height, points_str, algorithm_name):
    """Helper function to generate SVG content string."""
    # Generate SVG for valid grid points
    valid_grid_svg_list = []
    valid_point_radius = 1.5
    for vg_x, vg_y in valid_grid_points:
         valid_grid_svg_list.append(f'<circle cx="{vg_x:.7g}" cy="{vg_y:.7g}" r="{valid_point_radius}" fill="lightblue" opacity="0.7"/>')
    valid_grid_points_str = "\n  ".join(valid_grid_svg_list)

    # Generate SVG for the final placed points
    point_svg_list = []
    point_radius = 2.5
    point_color = "purple" # Color for this algorithm
    if timed_out: point_color = "gray" # Gray if timed out
    for p_x, p_y in points_to_draw:
         point_svg_list.append(f'<circle cx="{p_x:.7g}" cy="{p_y:.7g}" r="{point_radius}" fill="{point_color}"/>')
    point_elements_str = "\n  ".join(point_svg_list)

    # Generate SVG for minimum distance lines
    min_dist_line_svg_list = []
    for p1, p2 in min_dist_pairs:
         min_dist_line_svg_list.append(f'<line x1="{p1[0]:.7g}" y1="{p1[1]:.7g}" x2="{p2[0]:.7g}" y2="{p2[1]:.7g}" stroke="orange" stroke-width="1" stroke-dasharray="4 2" />')
    min_dist_lines_str = "\n  ".join(min_dist_line_svg_list)

    # Generate Grid lines
    grid_lines_str = ""
    if grid_info:
        grid_lines = []
        # Draw circumcircle and square used for grid generation
        cx = grid_info.get('cx')
        cy = grid_info.get('cy')
        radius = grid_info.get('radius')
        if cx is not None and cy is not None and radius is not None:
             grid_lines.append(f'<circle cx="{cx:.7g}" cy="{cy:.7g}" r="{radius:.7g}" stroke="gray" stroke-width="0.5" stroke-dasharray="3 3" fill="none" opacity="0.5"/>')
             min_c = grid_info.get('min_x', cx - radius) # Use calculated min/max if available
             max_c = grid_info.get('max_x', cx + radius)
             grid_lines.append(f'<rect x="{min_c:.7g}" y="{min_c:.7g}" width="{max_c - min_c:.7g}" height="{max_c - min_c:.7g}" stroke="gray" stroke-width="0.5" stroke-dasharray="3 3" fill="none" opacity="0.5"/>')

        # Draw initial grid lines
        for i in range(grid_info['num_divisions'] + 1):
            gx = grid_info['min_x'] + i * grid_info.get('step_x', 0)
            grid_lines.append(f'<line x1="{gx:.7g}" y1="{grid_info["min_y"]:.7g}" x2="{gx:.7g}" y2="{grid_info["max_y"]:.7g}" stroke="lightgray" stroke-width="0.5" />')
        for j in range(grid_info['num_divisions'] + 1):
            gy = grid_info['min_y'] + j * grid_info.get('step_y', 0)
            grid_lines.append(f'<line x1="{grid_info["min_x"]:.7g}" y1="{gy:.7g}" x2="{grid_info["max_x"]:.7g}" y2="{gy:.7g}" stroke="lightgray" stroke-width="0.5" />')
        grid_lines_str = "\n  ".join(grid_lines)

    # Comments
    status_comment = "Timed Out." if timed_out else "Completed."
    svg_comment = f""
    grid_comment = ""
    valid_points_comment = ""
    min_dist_comment = ""

    # Assemble SVG fragment
    svg_fragment = f"""
<svg
   width="100%"
   height="100%"
   viewBox="0 0 {svg_width} {svg_height}"
   preserveAspectRatio="xMidYMid meet"
   xmlns="http://www.w3.org/2000/svg">
  {grid_comment}
  {grid_lines_str}
  {valid_points_comment}
  {valid_grid_points_str}
  <polygon
     points="{points_str}"
     fill="none"
     stroke="black"
     stroke-width="2" />
  {min_dist_comment}
  {min_dist_lines_str}
  {svg_comment}
  {point_elements_str}
</svg>"""

    # Assemble full SVG content
    full_svg = f"""<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<svg
   width="{svg_width}"
   height="{svg_height}"
   viewBox="0 0 {svg_width} {svg_height}"
   xmlns="http://www.w3.org/2000/svg">
  {grid_comment}
  {grid_lines_str}
  {valid_points_comment}
  {valid_grid_points_str}
  <polygon
     points="{points_str}"
     fill="none"
     stroke="black"
     stroke-width="2" />
  {min_dist_comment}
  {min_dist_lines_str}
  {svg_comment}
  {point_elements_str}
</svg>"""

    return svg_fragment, full_svg


def generate_svg_data():
    """Generates SVG and HTML data, enables download and preview buttons."""
    global generated_svg_content_best, generated_svg_content_final
    global preview_html_content_best, preview_html_content_final
    global show_preview_button, show_final_button, download_button
    global overall_best_points_global, final_points_after_refinement # Store points globally

    # Disable buttons initially
    if show_preview_button: show_preview_button.config(state=tk.DISABLED)
    if show_final_button: show_final_button.config(state=tk.DISABLED)
    if download_button: download_button.config(state=tk.DISABLED)
    generated_svg_content_best = None
    preview_html_content_best = None
    generated_svg_content_final = None
    preview_html_content_final = None
    overall_best_points_global = []
    final_points_after_refinement = []


    # --- This is the main try block for the generation logic ---
    try:
        if not WEBVIEW_AVAILABLE:
            print("警告: pywebviewが見つからないため、プレビューは利用できません。")

        # --- Get Inputs ---
        num_sides_str = entry_sides.get()
        num_points_str = entry_points.get()
        num_divisions_str = entry_divisions.get()
        initial_time_limit_str = entry_initial_time_limit.get()
        refine_iterations_str = entry_refine_iterations.get()
        refine_time_limit_str = entry_refine_time_limit.get()

        if not num_sides_str: messagebox.showerror("エラー", "辺の数を入力してください。"); return
        if not num_points_str: messagebox.showerror("エラー", "点の数を入力してください。"); return
        if not num_divisions_str: messagebox.showerror("エラー", "初期格子分割数を入力してください。"); return
        if not initial_time_limit_str: messagebox.showerror("エラー", "最大初期探索時間を入力してください。"); return
        if not refine_iterations_str: messagebox.showerror("エラー", "最大改善反復回数を入力してください。"); return
        if not refine_time_limit_str: messagebox.showerror("エラー", "最大改善時間を入力してください。"); return

        num_sides = int(num_sides_str)
        num_points = int(num_points_str)
        num_divisions = int(num_divisions_str)
        initial_time_limit_sec = float(initial_time_limit_str)
        refine_iterations = int(refine_iterations_str)
        refine_time_limit_sec = float(refine_time_limit_str)

        if num_sides < 3: messagebox.showerror("エラー", "辺の数は3以上である必要があります。"); return
        if num_points < 2: messagebox.showerror("エラー", "点の数は2以上である必要があります。"); return
        if num_divisions < 1: messagebox.showerror("エラー", "格子分割数は1以上である必要があります。"); return
        if initial_time_limit_sec <= 0: messagebox.showerror("エラー", "最大初期探索時間は正の数である必要があります。"); return
        if refine_iterations < 0: messagebox.showerror("エラー", "最大改善反復回数は0以上である必要があります。"); return
        if refine_time_limit_sec < 0: messagebox.showerror("エラー", "最大改善時間は0以上である必要があります。"); return

        # --- SVG Configuration ---
        svg_width = 300
        svg_height = 300
        cx_poly = svg_width / 2
        cy_poly = svg_height / 2
        radius_poly = min(cx_poly, cy_poly) * 0.9 # Circumradius

        # --- Calculate Polygon Vertices ---
        polygon_vertices = parse_points_string(
            calculate_polygon_points(num_sides, cx_poly, cy_poly, radius_poly, rotation_offset_degrees=90)
        )
        if not polygon_vertices:
             messagebox.showerror("エラー", "ポリゴン頂点の生成に失敗しました。")
             return

        # --- Step 1: Initial Placement (Exhaustive Grid) ---
        initial_points, initial_timed_out, grid_info, valid_grid_points = find_initial_best_grid_comb(
            num_points, polygon_vertices, num_divisions, initial_time_limit_sec, cx_poly, cy_poly, radius_poly # Pass cx, cy, radius
        )

        if not initial_points:
             print("情報: 初期配置に失敗したため、処理を終了します。")
             return

        # --- Step 2: Refinement (Neighbor Combination Exhaustive Search) ---
        # Corrected function name call
        overall_best_points, final_points, refine_timed_out = refine_placement_neighbor_combinations_v3(
            initial_points, polygon_vertices, grid_info, refine_iterations, refine_time_limit_sec
        )

        # Store results globally
        overall_best_points_global = list(overall_best_points)
        final_points_after_refinement = list(final_points)

        # --- Generate SVG for the BEST result ---
        min_dist_pairs_best = []
        final_min_d2_best = min_sq_distance_in_set(overall_best_points_global)
        if final_min_d2_best != float('inf'):
            min_dist_pairs_best = find_min_dist_pairs(overall_best_points_global, final_min_d2_best)

        svg_fragment_best, generated_svg_content_best = generate_svg_content(
            overall_best_points_global, initial_timed_out or refine_timed_out, grid_info,
            valid_grid_points, min_dist_pairs_best, svg_width, svg_height,
            calculate_polygon_points(num_sides, cx_poly, cy_poly, radius_poly, rotation_offset_degrees=90),
            "Best Found"
        )
        preview_html_content_best = f"""
        <!DOCTYPE html><html><head><title>SVG Preview (Best Found)</title></head>
        <body style="margin:0; padding:0; display:flex; justify-content:center; align-items:center; height:100vh; background-color:#f0f0f0;">
        {svg_fragment_best}</body></html>"""

        # --- Generate SVG for the FINAL result ---
        min_dist_pairs_final = []
        final_min_d2_final = min_sq_distance_in_set(final_points_after_refinement)
        if final_min_d2_final != float('inf'):
            min_dist_pairs_final = find_min_dist_pairs(final_points_after_refinement, final_min_d2_final)

        svg_fragment_final, generated_svg_content_final = generate_svg_content(
            final_points_after_refinement, initial_timed_out or refine_timed_out, grid_info,
            valid_grid_points, min_dist_pairs_final, svg_width, svg_height,
            calculate_polygon_points(num_sides, cx_poly, cy_poly, radius_poly, rotation_offset_degrees=90),
            "Final State"
        )
        preview_html_content_final = f"""
        <!DOCTYPE html><html><head><title>SVG Preview (Final State)</title></head>
        <body style="margin:0; padding:0; display:flex; justify-content:center; align-items:center; height:100vh; background-color:#f0f0f0;">
        {svg_fragment_final}</body></html>"""


        # --- Enable Buttons ---
        if overall_best_points_global: # Enable if we have at least the initial result
            if download_button: download_button.config(state=tk.NORMAL) # Download always saves the best
            if WEBVIEW_AVAILABLE and show_preview_button:
                 show_preview_button.config(state=tk.NORMAL) # Show best
            if WEBVIEW_AVAILABLE and show_final_button:
                 show_final_button.config(state=tk.NORMAL) # Show final
            print("情報: SVGデータを生成しました。プレビューまたはダウンロードが可能です。")
        else:
             print("情報: 有効な点の配置が見つからなかったか、計算が失敗しました。")


    # --- Except blocks for the main try block ---
    except ValueError:
        messagebox.showerror("エラー", "有効な数値（整数または小数）を入力してください。")
    except Exception as e:
        # Print detailed error traceback to console
        print("--- エラー発生 ---")
        traceback.print_exc()
        print("-----------------")
        messagebox.showerror("予期せぬエラー", f"データ生成中にエラーが発生しました:\n{e}\n\n詳細はコンソールを確認してください。") # Added console instruction

def download_svg():
    # Opens a save dialog and saves the generated SVG content (always saves the BEST result).
    global generated_svg_content_best
    if not generated_svg_content_best:
        messagebox.showwarning("ダウンロード不可", "先にSVGデータを生成してください。")
        return

    try:
         num_sides = int(entry_sides.get())
         num_points_requested = int(entry_points.get())
         num_divisions = int(entry_divisions.get())
         initial_filename = f"polygon_{num_sides}_points_{num_points_requested}_grid{num_divisions}_neighbor_comb_best.svg" # Updated filename
    except ValueError:
         initial_filename = "polygon_points_neighbor_comb_best.svg"

    filepath = filedialog.asksaveasfilename(
        defaultextension=".svg",
        filetypes=[("SVG ファイル", "*.svg"), ("すべてのファイル", "*.*")],
        initialfile=initial_filename,
        title="SVGファイルを保存 (最良配置)" # Save SVG File (Best Placement)
    )

    if not filepath: return

    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(generated_svg_content_best) # Save the best SVG
        messagebox.showinfo("成功", f"SVGファイル(最良配置)が正常に保存されました:\n{os.path.basename(filepath)}") # Success: SVG file (best placement) saved successfully:
    except Exception as e:
        messagebox.showerror("ファイル保存エラー", f"ファイルの書き込み中にエラーが発生しました:\n{e}")


# --- GUI Setup ---
root = tk.Tk()
root.title("多角形と点配置(ExhGrid+NeighborComb)SVG生成") # Updated Title
root.geometry("450x400") # Adjusted height

# Main frame
frame = ttk.Frame(root, padding="10")
frame.pack(expand=True, fill=tk.BOTH)

# Input frame (top part)
input_frame = ttk.Frame(frame)
input_frame.pack(fill=tk.X, pady=5)
label_sides = ttk.Label(input_frame, text="正多角形の辺の数:")
label_sides.grid(row=0, column=0, padx=5, pady=2, sticky=tk.W)
entry_sides = ttk.Entry(input_frame, width=10, justify='center')
entry_sides.grid(row=0, column=1, padx=5, pady=2)

label_points = ttk.Label(input_frame, text="内部に配置する点の数:")
label_points.grid(row=1, column=0, padx=5, pady=2, sticky=tk.W)
entry_points = ttk.Entry(input_frame, width=10, justify='center')
entry_points.grid(row=1, column=1, padx=5, pady=2)
entry_points.insert(0, "4") # Default number of points (keep VERY low for this algorithm)

label_divisions = ttk.Label(input_frame, text="初期格子分割数 (N):")
label_divisions.grid(row=2, column=0, padx=5, pady=2, sticky=tk.W)
entry_divisions = ttk.Entry(input_frame, width=10, justify='center')
entry_divisions.grid(row=2, column=1, padx=5, pady=2)
entry_divisions.insert(0, "5") # Default number of divisions (keep low)

label_initial_time_limit = ttk.Label(input_frame, text="最大初期探索時間 (秒):")
label_initial_time_limit.grid(row=3, column=0, padx=5, pady=2, sticky=tk.W)
entry_initial_time_limit = ttk.Entry(input_frame, width=10, justify='center')
entry_initial_time_limit.grid(row=3, column=1, padx=5, pady=2)
entry_initial_time_limit.insert(0, "5") # Default initial time limit

label_refine_iterations = ttk.Label(input_frame, text="最大改善反復回数:") # Label for refinement iterations
label_refine_iterations.grid(row=4, column=0, padx=5, pady=2, sticky=tk.W)
entry_refine_iterations = ttk.Entry(input_frame, width=10, justify='center') # Entry for refinement iterations
entry_refine_iterations.grid(row=4, column=1, padx=5, pady=2)
entry_refine_iterations.insert(0, "1") # Default refinement iterations (keep VERY low)

label_refine_time_limit = ttk.Label(input_frame, text="最大改善時間 (秒):") # Label for refinement time limit
label_refine_time_limit.grid(row=5, column=0, padx=5, pady=2, sticky=tk.W)
entry_refine_time_limit = ttk.Entry(input_frame, width=10, justify='center') # Entry for refinement time limit
entry_refine_time_limit.grid(row=5, column=1, padx=5, pady=2)
entry_refine_time_limit.insert(0, "10") # Default refinement time limit

entry_sides.focus()

# --- Buttons Frame ---
button_frame = ttk.Frame(frame)
button_frame.pack(fill=tk.X, pady=5)

# Button to generate data
generate_button = ttk.Button(button_frame, text="SVGデータ生成", command=generate_svg_data)
generate_button.pack(side=tk.LEFT, padx=5)

# Button to show the BEST result preview window (initially disabled)
show_preview_button = ttk.Button(button_frame, text="最良結果表示", command=lambda: show_actual_preview_window("best"), state=tk.DISABLED) # Show Best Result
show_preview_button.pack(side=tk.LEFT, padx=5)

# Button to show the FINAL result preview window (initially disabled)
show_final_button = ttk.Button(button_frame, text="最終結果表示", command=lambda: show_actual_preview_window("final"), state=tk.DISABLED) # Show Final Result
show_final_button.pack(side=tk.LEFT, padx=5)

# Button to download the BEST result (initially disabled)
download_button = ttk.Button(button_frame, text="SVG保存(最良)", command=download_svg, state=tk.DISABLED) # Download SVG (Best)
download_button.pack(side=tk.LEFT, padx=5)


# --- Preview Area Placeholder ---
preview_info_frame = ttk.Frame(frame, padding=(0, 10))
preview_info_frame.pack(fill=tk.X, expand=True)

preview_label_text = ttk.Label(preview_info_frame, text="ボタンクリックで別ウィンドウにプレビュー表示", anchor=tk.CENTER) # Click buttons to show preview in separate window.
preview_label_text.pack(pady=10)

# Check if library is available and inform user if not
if not WEBVIEW_AVAILABLE:
     lib_error_label = ttk.Label(preview_info_frame, text="プレビュー機能には 'pywebview' が必要です。\n'pip install pywebview' を実行してください。", foreground="red", anchor=tk.CENTER)
     lib_error_label.pack(pady=5)
     if show_preview_button: show_preview_button.config(state=tk.DISABLED)
     if show_final_button: show_final_button.config(state=tk.DISABLED)


root.mainloop()
