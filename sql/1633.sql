SELECT  t1.contest_id
       ,round(cast(div((COUNT(t2.user_id)) * 100,COUNT(t1.user_id)) AS numeric),2) AS percentage
FROM
(
	SELECT  *
	FROM
	(
		SELECT  distinct register.contest_id
		FROM register
	) AS co
	CROSS JOIN
	(
		SELECT  distinct users.user_id
		FROM users
	) AS us
) AS t1
LEFT JOIN register AS t2
ON (t1.contest_id = t2.contest_id) AND (t1.user_id = t2.user_id)
GROUP BY  t1.contest_id
ORDER BY percentage desc
         ,t1.contest_id asc