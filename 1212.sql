SELECT  t.team_id
       ,t.team_name
       ,(SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals > m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals < m.guest_goals)) THEN 3 ELSE 0 END)) + (SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals = m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals = m.guest_goals)) THEN 1 ELSE 0 END)) AS num_points
FROM Teams AS t
CROSS JOIN Matches AS m
GROUP BY  t.team_id
         ,t.team_name
ORDER BY num_points DESC
         ,t.team_id ASC