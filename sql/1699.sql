WITH all_users AS
(
       SELECT  distinct calls.from_id AS id
       FROM calls union
       SELECT  distinct calls.to_id AS id
       FROM calls
)
SELECT  a.id            AS person1
       ,b.id            AS person2
       ,COUNT(c.duration) AS call_count
       ,SUM(c.duration)   AS total_duration
FROM      all_users a
     JOIN all_users b ON a.id<b.id
     JOIN calls c ON (a.id = c.from_id AND b.id = c.to_id ) or (a.id = c.to_id AND b.id = c.from_id )
GROUP BY  a.id
         ,b.id